-- Prove2me | solution 1 for Module.Grassmannian.existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b1e878fd-18fd-5268-854e-647c129f94c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace GrassSheafS1b

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

section structureMap

variable (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B]

noncomputable def l : A ⊗[R] M →ₗ[A] B ⊗[R] M :=
  AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)

@[scoped simp] lemma l_tmul (a : A) (m : M) : l R M A B (a ⊗ₜ[R] m) = algebraMap A B a ⊗ₜ[R] m := by
  simp [l]

scoped instance (S : Submonoid A) [IsLocalization S B] : IsLocalizedModule S (l R M A B) := by
  unfold l; infer_instance

lemma baseChangeMkQ_l (N : Submodule A (A ⊗[R] M)) (m : A ⊗[R] M) :
    Module.Grassmannian.baseChangeMkQ B N (l R M A B m) = (1 : B) ⊗ₜ[A] N.mkQ m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [l_tmul, Module.Grassmannian.baseChangeMkQ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      Algebra.algebraMap_eq_smul_one, smul_tmul, ← map_smul, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, tmul_add]

variable {A B} in

lemma map_toSubmodule' {k : ℕ} (f : A →ₐ[R] B) (hf : ∀ a, algebraMap A B a = f a)
    (N : Module.Grassmannian A (A ⊗[R] M) k) :
    (Module.Grassmannian.map f N).toSubmodule =
      LinearMap.ker (Module.Grassmannian.baseChangeMkQ B N.toSubmodule) := by
  have h : ‹Algebra A B› = f.toAlgebra :=
    Algebra.algebra_ext _ _ fun a => by rw [hf]; rfl
  subst h
  exact Module.Grassmannian.map_toSubmodule f N

lemma ker_baseChangeMkQ_eq_localized' (S : Submonoid A) [IsLocalization S B]
    (N : Submodule A (A ⊗[R] M)) :
    LinearMap.ker (Module.Grassmannian.baseChangeMkQ B N) = N.localized' B S (l R M A B) := by
  have key : (Module.Grassmannian.baseChangeMkQ B N).restrictScalars A =
      IsLocalizedModule.map S (l R M A B) (TensorProduct.mk A B ((A ⊗[R] M) ⧸ N) 1) N.mkQ := by
    apply IsLocalizedModule.linearMap_ext S (l R M A B) (TensorProduct.mk A B ((A ⊗[R] M) ⧸ N) 1)
    rw [IsLocalizedModule.map_comp]
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, baseChangeMkQ_l]
    rfl
  apply Submodule.restrictScalars_injective A
  rw [← LinearMap.ker_restrictScalars, key,
    LinearMap.ker_localizedMap_eq_localized'_ker B S (l R M A B)
      (TensorProduct.mk A B ((A ⊗[R] M) ⧸ N) 1) N.mkQ, Submodule.ker_mkQ]

end structureMap

section tower

variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B]
  [Algebra R C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [IsScalarTower R A B] [IsScalarTower R B C] [IsScalarTower R A C]

lemma l_l (m : A ⊗[R] M) : l R M B C (l R M A B m) = l R M A C m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end tower

section glue

variable {k : ℕ}
variable (A : Type) [CommRing A] [Algebra R A] {n : ℕ} (f : Fin n → A)
  (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
  [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
  (N : ∀ i, Module.Grassmannian (B i) (B i ⊗[R] M) k)

def Cocycle : Prop :=
  ∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
    Module.Grassmannian.map (ρ₁.restrictScalars R) (N i) =
      Module.Grassmannian.map (ρ₂.restrictScalars R) (N j)

variable {A f B N}

lemma exists_pow_smul_mem (hN : Cocycle R M A f B N) (i j : Fin n) (m : A ⊗[R] M)
    (hm : l R M A (B i) m ∈ (N i).toSubmodule) :
    ∃ a : ℕ, l R M A (B j) (f i ^ a • m) ∈ (N j).toSubmodule := by
  let C := Localization.Away (algebraMap A (B j) (f i))
  have hu : ∀ y : Submonoid.powers (f i), IsUnit (Algebra.ofId A C y) := by
    rintro ⟨_, a, rfl⟩
    rw [map_pow]
    refine IsUnit.pow _ ?_
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A (B j) C]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap A (B j) (f i))
  let ρ₁ : B i →ₐ[A] C := IsLocalization.liftAlgHom (M := Submonoid.powers (f i)) hu
  let ρ₂ : B j →ₐ[A] C := IsScalarTower.toAlgHom A (B j) C
  have hcoc := hN i j C ρ₁ ρ₂
  have h1 : l R M A C m ∈
      (Module.Grassmannian.map (ρ₁.restrictScalars R) (N i)).toSubmodule := by
    letI : Algebra (B i) C := (ρ₁.restrictScalars R).toAlgebra
    haveI : IsScalarTower R (B i) C :=
      IsScalarTower.of_algebraMap_eq' (ρ₁.restrictScalars R).comp_algebraMap.symm
    haveI : IsScalarTower A (B i) C :=
      IsScalarTower.of_algebraMap_eq fun a => (ρ₁.commutes a).symm
    rw [map_toSubmodule' R M (ρ₁.restrictScalars R) (fun _ => rfl), LinearMap.mem_ker,
      ← l_l R M A (B i) C, baseChangeMkQ_l]
    have : (N i).toSubmodule.mkQ (l R M A (B i) m) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hm
    rw [this, tmul_zero]
  rw [hcoc, map_toSubmodule' R M (ρ₂.restrictScalars R) (fun _ => rfl), LinearMap.mem_ker,
    ← l_l R M A (B j) C, baseChangeMkQ_l] at h1
  obtain ⟨⟨_, a, rfl⟩, ha⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers (algebraMap A (B j) (f i)))
      (TensorProduct.mk (B j) C ((B j ⊗[R] M) ⧸ (N j).toSubmodule) 1)).mp h1
  refine ⟨a, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, map_smul, Submodule.Quotient.mk_smul]
  simpa [Submonoid.mk_smul, ← map_pow, algebraMap_smul] using ha

variable (A B N) in

noncomputable def glued : Submodule A (A ⊗[R] M) :=
  ⨅ i, ((N i).toSubmodule.restrictScalars A).comap (l R M A (B i))

lemma mem_glued {m : A ⊗[R] M} :
    m ∈ glued R M A B N ↔ ∀ i, l R M A (B i) m ∈ (N i).toSubmodule := by
  simp [glued, Submodule.mem_iInf]

lemma localized'_glued (hN : Cocycle R M A f B N) (i : Fin n) :
    (glued R M A B N).localized' (B i) (Submonoid.powers (f i)) (l R M A (B i)) =
      (N i).toSubmodule := by
  apply le_antisymm
  · rw [Submodule.localized'_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_glued R M).mp hm i
  · intro y hy
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective (Submonoid.powers (f i)) (l R M A (B i)) y
    simp only [Function.uncurry_apply_pair] at hy ⊢
    have hlm : l R M A (B i) m ∈ (N i).toSubmodule := by
      rw [← IsLocalizedModule.mk'_cancel' (l R M A (B i)) m s]
      exact Submodule.smul_of_tower_mem _ s hy
    choose a ha using fun j => exists_pow_smul_mem R M hN i j m hlm
    let e : ℕ := Finset.univ.sup a
    have hmem : f i ^ e • m ∈ glued R M A B N := by
      rw [mem_glued]
      intro j
      have : f i ^ e • m = f i ^ (e - a j) • (f i ^ a j • m) := by
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ j))]
      rw [this, map_smul]
      exact Submodule.smul_of_tower_mem _ _ (ha j)
    let t : Submonoid.powers (f i) := ⟨f i ^ e, e, rfl⟩
    refine ⟨f i ^ e • m, hmem, t * s, ?_⟩
    rw [← IsLocalizedModule.mk'_cancel_left (l R M A (B i)) m t s]
    rfl

variable (A B N) in

abbrev Q0 : Type := (A ⊗[R] M) ⧸ glued R M A B N

noncomputable def gq (hN : Cocycle R M A f B N) (i : Fin n) :
    Q0 R M A B N →ₗ[A] (B i ⊗[R] M) ⧸ (N i).toSubmodule :=
  ((Submodule.quotEquivOfEq _ _ (localized'_glued R M hN i)).restrictScalars A).toLinearMap ∘ₗ
    (glued R M A B N).toLocalizedQuotient' (B i) (Submonoid.powers (f i)) (l R M A (B i))

scoped instance (hN : Cocycle R M A f B N) (i : Fin n) :
    IsLocalizedModule (Submonoid.powers (f i)) (gq R M hN i) := by
  unfold gq; infer_instance

variable (f) in

noncomputable def idx (r : Set.range f) : Fin n := r.2.choose

omit [CommRing A] in
omit [CommRing A] in
lemma f_idx (r : Set.range f) : f (idx f r) = r.1 := r.2.choose_spec

lemma away_idx (r : Set.range f) : IsLocalization.Away r.1 (B (idx f r)) := by
  rw [← f_idx r]; infer_instance

lemma isLocalizedModule_idx (hN : Cocycle R M A f B N) (r : Set.range f) :
    IsLocalizedModule (Submonoid.powers r.1) (gq R M hN (idx f r)) := by
  rw [← f_idx r]; infer_instance

lemma isLocalizedModule_l_idx (r : Set.range f) :
    IsLocalizedModule (Submonoid.powers r.1) (l R M A (B (idx f r))) := by
  rw [← f_idx r]; infer_instance

lemma finite_Q0 (hf : Ideal.span (Set.range f) = ⊤) (hN : Cocycle R M A f B N) :
    Module.Finite A (Q0 R M A B N) := by
  haveI := fun r => away_idx (f := f) (B := B) r
  haveI := isLocalizedModule_idx R M hN
  exact Module.Finite.of_localizationSpan' (Set.range f) hf
    (Rₚ := fun r => B (idx f r)) (Mₚ := fun r => (B (idx f r) ⊗[R] M) ⧸ (N (idx f r)).toSubmodule)
    (fun r => gq R M hN (idx f r)) fun r => inferInstance

lemma finitePresentation_Q0 (hf : Ideal.span (Set.range f) = ⊤) (hN : Cocycle R M A f B N) :
    Module.FinitePresentation A (Q0 R M A B N) := by
  haveI := fun r => away_idx (f := f) (B := B) r
  haveI := isLocalizedModule_idx R M hN
  exact Module.FinitePresentation.of_localizationSpan' (Set.range f) hf
    (Rₚ := fun r => B (idx f r)) (Mₚ := fun r => (B (idx f r) ⊗[R] M) ⧸ (N (idx f r)).toSubmodule)
    (fun r => gq R M hN (idx f r)) fun r => Module.finitePresentation_of_projective _ _

lemma exists_not_mem (hf : Ideal.span (Set.range f) = ⊤) (p : PrimeSpectrum A) :
    ∃ i, f i ∉ p.asIdeal := by
  by_contra! h
  apply p.2.ne_top
  rw [eq_top_iff, ← hf, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
lemma projective_localizedModule (hN : Cocycle R M A f B N) (i : Fin n) :
    Module.Projective (Localization.Away (f i)) (LocalizedModule.Away (f i) (Q0 R M A B N)) := by
  set e := (IsLocalization.algEquiv (Submonoid.powers (f i)) (B i)
    (Localization.Away (f i))).toRingEquiv
  refine Module.Projective.of_equiv (M := (B i ⊗[R] M) ⧸ (N i).toSubmodule) (R := B i) (σ := e)
    { __ := IsLocalizedModule.linearEquiv (Submonoid.powers (f i)) (gq R M hN i)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (Q0 R M A B N))
      map_smul' := ?_ }
  intro r m
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (f i)) r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (Q0 R M A B N)) s)).1
  dsimp [e]
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
    IsLocalization.map_id_mk', AlgEquiv.commutes]

lemma projective_Q0 (hf : Ideal.span (Set.range f) = ⊤) (hN : Cocycle R M A f B N) :
    Module.Projective A (Q0 R M A B N) := by
  haveI := finitePresentation_Q0 R M hf hN
  rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  obtain ⟨i, hi⟩ := exists_not_mem hf p
  exact Module.basicOpen_subset_freeLocus_iff.mpr (projective_localizedModule R M hN i) hi

noncomputable def baseChangeEquiv (hN : Cocycle R M A f B N) (i : Fin n) :
    B i ⊗[A] Q0 R M A B N ≃ₗ[B i] (B i ⊗[R] M) ⧸ (N i).toSubmodule :=
  (IsLocalizedModule.linearEquiv (Submonoid.powers (f i))
      (TensorProduct.mk A (B i) (Q0 R M A B N) 1) (gq R M hN i)).extendScalarsOfIsLocalization
    (Submonoid.powers (f i)) (B i)

lemma rankAtStalk_Q0 (hf : Ideal.span (Set.range f) = ⊤) (hN : Cocycle R M A f B N)
    (p : PrimeSpectrum A) : Module.rankAtStalk (Q0 R M A B N) p = k := by
  haveI := projective_Q0 R M hf hN
  haveI := finite_Q0 R M hf hN
  obtain ⟨i, hi⟩ := exists_not_mem hf p
  obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (B i))) := by
    rw [PrimeSpectrum.localization_away_comap_range (B i) (f i)]
    exact hi
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv (baseChangeEquiv R M hN i),
    (N i).rankAtStalk_eq q]

noncomputable def gluedGr (hf : Ideal.span (Set.range f) = ⊤) (hN : Cocycle R M A f B N) :
    Module.Grassmannian A (A ⊗[R] M) k where
  toSubmodule := glued R M A B N
  finite_quotient := finite_Q0 R M hf hN
  projective_quotient := projective_Q0 R M hf hN
  rankAtStalk_eq := rankAtStalk_Q0 R M hf hN

end glue

end GrassSheafS1b
p2m_reactivate "P2MW.S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away.GrassSheafS1b"

open GrassSheafS1b in
theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ)
    (A : Type) [CommRing A] [Algebra R A] (n : ℕ) (f : Fin n → A) (hf : Ideal.span (Set.range f) = ⊤)
    (B : Fin n → Type) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra R (B i)]
    [∀ i, IsScalarTower R A (B i)] [∀ i, IsLocalization.Away (f i) (B i)]
    (N : ∀ i, Module.Grassmannian (B i) (B i ⊗[R] M) k)
    (hN : ∀ (i j : Fin n) (C : Type) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
        [IsLocalization.Away (f i * f j) C] (ρ₁ : B i →ₐ[A] C) (ρ₂ : B j →ₐ[A] C),
        Module.Grassmannian.map (ρ₁.restrictScalars R) (N i) =
          Module.Grassmannian.map (ρ₂.restrictScalars R) (N j)) :
    ∃! N₀ : Module.Grassmannian A (A ⊗[R] M) k,
      ∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (B i)) N₀ = N i := by
  have hN' : Cocycle R M A f B N := hN

  have key : ∀ (N₀ : Module.Grassmannian A (A ⊗[R] M) k) (i : Fin n) (S : Submonoid A)
      [IsLocalization S (B i)],
      (Module.Grassmannian.map (IsScalarTower.toAlgHom R A (B i)) N₀).toSubmodule =
        N₀.toSubmodule.localized' (B i) S (l R M A (B i)) := fun N₀ i S _ => by
    rw [map_toSubmodule' R M (IsScalarTower.toAlgHom R A (B i)) (fun _ => rfl),
      ker_baseChangeMkQ_eq_localized' R M A (B i) S]
  have hglued : ∀ i, Module.Grassmannian.map (IsScalarTower.toAlgHom R A (B i))
      (gluedGr R M hf hN') = N i := fun i => by
    ext1
    rw [key _ i (Submonoid.powers (f i))]
    exact localized'_glued R M hN' i
  refine ⟨gluedGr R M hf hN', hglued, fun N₀ h => ?_⟩
  ext1
  haveI := fun r => away_idx (f := f) (B := B) r
  haveI := fun r => isLocalizedModule_l_idx R M (f := f) (B := B) r
  refine Submodule.eq_of_isLocalized'_span (Set.range f) hf (fun r => B (idx f r))
    (fun r => B (idx f r) ⊗[R] M) (fun r => l R M A (B (idx f r))) fun r => ?_
  rw [← key N₀ (idx f r) (Submonoid.powers r.1), ← key (gluedGr R M hf hN') (idx f r)
    (Submonoid.powers r.1), h, hglued]

end S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away
end P2MW
export P2MW.S_Module_Grassmannian_existsUnique_forall_map_toAlgHom_eq_of_isLocalization_away (solution)

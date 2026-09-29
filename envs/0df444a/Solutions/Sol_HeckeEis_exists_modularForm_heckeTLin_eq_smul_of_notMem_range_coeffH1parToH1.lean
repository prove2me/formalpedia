-- Prove2me | solution 1 for HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/04f358bd-14bc-545f-b4d8-839dffb2b9e6

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffParabolicCocycles
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_exists_isEichlerIntegral
import Theorems.Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
import Theorems.Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const
import Theorems.Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm
import Theorems.Thm_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles
import Theorems.Thm_ModularForm_finiteDimensional_Gamma0
import Theorems.Thm_ModularForm_heckeTLin_comm
import Theorems.Thm_Module_exists_ne_zero_forall_smul_eq_smul_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1

set_option autoImplicit false

namespace A2W1E

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups Manifold ModularForm

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

theorem unique_of_isCoeffHeckeOnH1 {T T' : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T)
    (hT' : IsCoeffHeckeOnH1 N ℓ ρ a T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨w', hw', hTw'⟩ := hT' z
  rw [hTw, hTw']
  congr 1
  exact Subtype.ext (hw.trans hw'.symm)

def parSub (ρ : Representation K (Gamma0 N) V) : Submodule K ↥(coeffCocycles ρ) :=
  (coeffParabolicCocycles ρ).comap (coeffCocycles ρ).subtype

theorem range_coeffH1parToH1 (ρ : Representation K (Gamma0 N) V) :
    LinearMap.range (coeffH1parToH1 ρ) = (parSub ρ).map (coeffH1Mk ρ) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := coeffH1parMk_surjective ρ x
    rw [coeffH1parToH1_coeffH1parMk]
    exact ⟨Submodule.inclusion (coeffParabolicCocycles_le_coeffCocycles ρ) w, w.2, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨coeffH1parMk ρ ⟨z, hz⟩, ?_⟩
    rw [coeffH1parToH1_coeffH1parMk]
    rfl

theorem coeffH1Mk_mem_range_of_mem {ρ : Representation K (Gamma0 N) V} {z : ↥(coeffCocycles ρ)}
    (hz : (z : Gamma0 N → V) ∈ coeffParabolicCocycles ρ) :
    coeffH1Mk ρ z ∈ LinearMap.range (coeffH1parToH1 ρ) := by
  rw [range_coeffH1parToH1]
  exact ⟨z, hz, rfl⟩

theorem heckeH1_mem_range (ha : IsCompat N ℓ ρ a) {x : coeffH1 ρ}
    (hx : x ∈ LinearMap.range (coeffH1parToH1 ρ)) :
    heckeH1 ha x ∈ LinearMap.range (coeffH1parToH1 ρ) := by
  rw [range_coeffH1parToH1] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  rw [heckeH1_mk]
  exact ⟨heckeZ1 ha z, coeffHeckeFun_mem_coeffParabolicCocycles N ℓ ρ a ha hz, rfl⟩

end Induced

section ES

variable (N : ℕ) (n : ℕ)

noncomputable abbrev ρC : Representation ℂ (Gamma0 N) ↥(BinaryForm ℂ n) :=
  (binaryFormRepSL ℂ n).comp (Gamma0 N).subtype

abbrev MF : Type := ModularForm (Gamma0 N) ((n : ℤ) + 2)

variable {N n}

theorem mdifferentiable_coe (f : MF N n) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f) := ModularFormClass.holo f

theorem slash_eq_of_mem (f : MF N n) : ∀ γ ∈ Gamma0 N, (⇑f) ∣[((n : ℤ) + 2)] γ = ⇑f := fun γ hγ =>
  SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) (Subgroup.mem_map_of_mem _ hγ)

noncomputable def eichler (f : MF N n) : UpperHalfPlane → ↥(BinaryForm ℂ n) :=
  (exists_isEichlerIntegral n (mdifferentiable_coe f)).choose

theorem isEichlerIntegral_eichler (f : MF N n) : IsEichlerIntegral n (⇑f) (eichler f) :=
  (exists_isEichlerIntegral n (mdifferentiable_coe f)).choose_spec

theorem equiv_eichler (f : MF N n) : IsEquivariantPrimitiveWith (ρC N n) (eichler f) :=
  isEquivariantPrimitiveWith_of_isEichlerIntegral (isEichlerIntegral_eichler f) (slash_eq_of_mem f)

noncomputable def esClass (f : MF N n) : coeffH1 (ρC N n) :=
  coeffH1Mk (ρC N n) ⟨(equiv_eichler f).cocycle, (equiv_eichler f).cocycle_mem_coeffCocycles⟩

theorem coeffH1Mk_eq_esClass (f : MF N n) {F : UpperHalfPlane → ↥(BinaryForm ℂ n)}
    (hEI : IsEichlerIntegral n (⇑f) F) (hF : IsEquivariantPrimitiveWith (ρC N n) F) :
    coeffH1Mk (ρC N n) ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩ = esClass f := by
  obtain ⟨v, hv⟩ := hEI.exists_sub_eq_const (isEichlerIntegral_eichler f)
  have hcob := hF.cocycle_sub_cocycle_mem_coeffCoboundaries (equiv_eichler f) hv
  exact (Submodule.Quotient.eq _).mpr hcob

theorem isEichlerIntegral_add {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (hG : IsEichlerIntegral n g G) :
    IsEichlerIntegral n (f + g) (fun τ => F τ + G τ) := by
  intro d τ
  have h := (hF d τ).add (hG d τ)
  simp only [Submodule.coe_add, MvPolynomial.coeff_add, Pi.add_apply]
  convert h using 1
  · rfl
  · rfl
  · rfl
  ring

theorem isEichlerIntegral_smul {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (c : ℂ) :
    IsEichlerIntegral n (c • f) (fun τ => c • F τ) := by
  intro d τ
  have h := (hF d τ).const_mul c
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, Pi.smul_apply]
  convert h using 1
  · rfl
  · rfl
  ring

theorem isEquivariantPrimitiveWith_add {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V]
    [Module K V] {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (hG : IsEquivariantPrimitiveWith ρ G) :
    ∃ hFG : IsEquivariantPrimitiveWith ρ (fun τ => F τ + G τ), hFG.cocycle = hF.cocycle + hG.cocycle := by
  have hFG : IsEquivariantPrimitiveWith ρ (fun τ => F τ + G τ) := by
    intro γ
    refine ⟨hF.cocycle γ + hG.cocycle γ, fun τ => ?_⟩
    have h1 := hF.apply_smul γ τ
    have h2 := hG.apply_smul γ τ
    dsimp only
    rw [h1, h2, map_add]
    abel
  refine ⟨hFG, funext fun γ => ?_⟩
  simp only [IsEquivariantPrimitiveWith.cocycle, Pi.add_apply, map_add]
  abel

theorem isEquivariantPrimitiveWith_smul {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V]
    [Module K V] {ρ : Representation K Γ V} {F : UpperHalfPlane → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (c : K) :
    ∃ hcF : IsEquivariantPrimitiveWith ρ (fun τ => c • F τ), hcF.cocycle = c • hF.cocycle := by
  have hcF : IsEquivariantPrimitiveWith ρ (fun τ => c • F τ) := by
    intro γ
    refine ⟨c • hF.cocycle γ, fun τ => ?_⟩
    have h1 := hF.apply_smul γ τ
    dsimp only
    rw [h1, map_smul, smul_add, add_sub_cancel_right]
  refine ⟨hcF, funext fun γ => ?_⟩
  simp only [IsEquivariantPrimitiveWith.cocycle, Pi.smul_apply, map_smul, smul_sub]

theorem esClass_add (f g : MF N n) : esClass (f + g) = esClass f + esClass g := by
  have hEI : IsEichlerIntegral n (⇑(f + g)) (fun τ => eichler f τ + eichler g τ) := by
    rw [ModularForm.coe_add]
    exact isEichlerIntegral_add (isEichlerIntegral_eichler f) (isEichlerIntegral_eichler g)
  obtain ⟨hFG, hcoc⟩ := isEquivariantPrimitiveWith_add (equiv_eichler f) (equiv_eichler g)
  rw [← coeffH1Mk_eq_esClass (f + g) hEI hFG, esClass, esClass, ← map_add]
  congr 1
  exact Subtype.ext hcoc

theorem esClass_smul (c : ℂ) (f : MF N n) : esClass (c • f) = c • esClass f := by
  have hEI : IsEichlerIntegral n (⇑(c • f)) (fun τ => c • eichler f τ) := by
    rw [ModularForm.IsGLPos.coe_smul]
    exact isEichlerIntegral_smul (isEichlerIntegral_eichler f) c
  obtain ⟨hcF, hcoc⟩ := isEquivariantPrimitiveWith_smul (equiv_eichler f) c
  rw [← coeffH1Mk_eq_esClass (c • f) hEI hcF, esClass, ← map_smul]
  congr 1
  exact Subtype.ext hcoc

variable (N n) in

noncomputable def esLin : MF N n →ₗ[ℂ] coeffH1 (ρC N n) where
  toFun := esClass
  map_add' := esClass_add
  map_smul' := esClass_smul

@[scoped simp] theorem esLin_apply (f : MF N n) : esLin N n f = esClass f := rfl

end ES

section Hecke

variable (N : ℕ) (n : ℕ)

theorem isCompat (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρC N n) (binaryFormAlphaAdj ℂ n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ u

noncomputable def TH {ℓ : ℕ} (hℓ : ℓ.Prime) : coeffH1 (ρC N n) →ₗ[ℂ] coeffH1 (ρC N n) :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  heckeH1 (isCompat N n ℓ)

theorem isCoeffHeckeOnH1_TH {ℓ : ℕ} (hℓ : ℓ.Prime) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    IsCoeffHeckeOnH1 N ℓ (ρC N n) (binaryFormAlphaAdj ℂ n ℓ) (TH N n hℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact isCoeffHeckeOnH1_heckeH1 (isCompat N n ℓ)

theorem TH_mem_range {ℓ : ℕ} (hℓ : ℓ.Prime) {x : coeffH1 (ρC N n)}
    (hx : x ∈ LinearMap.range (coeffH1parToH1 (ρC N n))) :
    TH N n hℓ x ∈ LinearMap.range (coeffH1parToH1 (ρC N n)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact heckeH1_mem_range (isCompat N n ℓ) hx

theorem TH_esLin [NeZero N] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : MF N n) :
    TH N n hℓ (esLin N n f) = esLin N n (ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f) := by
  rw [esLin_apply, esLin_apply, esClass, esClass]
  exact coeffH1Mk_cocycle_heckeTLin_modularForm N n hℓ hℓN (TH N n hℓ) (isCoeffHeckeOnH1_TH N n hℓ) f
    (eichler f) (isEichlerIntegral_eichler f) (equiv_eichler f)
    (eichler _) (isEichlerIntegral_eichler _) (equiv_eichler _)

end Hecke

section Boundary

variable (N : ℕ) [NeZero N] (n : ℕ)

noncomputable abbrev Rpar : Submodule ℂ (coeffH1 (ρC N n)) := LinearMap.range (coeffH1parToH1 (ρC N n))

abbrev Q : Type := coeffH1 (ρC N n) ⧸ Rpar N n

noncomputable def Ψ : MF N n →ₗ[ℂ] Q N n := (Rpar N n).mkQ ∘ₗ esLin N n

noncomputable def TQ {ℓ : ℕ} (hℓ : ℓ.Prime) : Q N n →ₗ[ℂ] Q N n :=
  (Rpar N n).mapQ (Rpar N n) (TH N n hℓ) fun _ hx => TH_mem_range N n hℓ hx

omit [NeZero N] in
theorem TQ_mkQ {ℓ : ℕ} (hℓ : ℓ.Prime) (x : coeffH1 (ρC N n)) :
    TQ N n hℓ ((Rpar N n).mkQ x) = (Rpar N n).mkQ (TH N n hℓ x) := rfl

theorem TQ_Ψ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : MF N n) :
    TQ N n hℓ (Ψ N n f) = Ψ N n (ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f) := by
  change TQ N n hℓ ((Rpar N n).mkQ (esLin N n f)) = (Rpar N n).mkQ (esLin N n _)
  rw [TQ_mkQ, TH_esLin]

theorem Ψ_surjective : Function.Surjective (Ψ N n) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (Rpar N n) q
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective (ρC N n) x
  obtain ⟨f, F, hEI, hF, hpar⟩ := exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles N n z
  refine ⟨f, ?_⟩
  change (Rpar N n).mkQ (esLin N n f) = (Rpar N n).mkQ (coeffH1Mk (ρC N n) z)
  rw [esLin_apply, ← coeffH1Mk_eq_esClass f hEI hF, eq_comm, ← sub_eq_zero, ← map_sub, ← map_sub,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact coeffH1Mk_mem_range_of_mem hpar

end Boundary

section Lift

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def Descends (Ψ : V →ₗ[ℂ] W) (xbar : W) (a : Module.End ℂ V) : Prop :=
  ∃ (c : ℂ) (abar : W →ₗ[ℂ] W), Ψ ∘ₗ a = abar ∘ₗ Ψ ∧ abar xbar = c • xbar

theorem Descends.one (Ψ : V →ₗ[ℂ] W) (xbar : W) : Descends Ψ xbar 1 :=
  ⟨1, LinearMap.id, by ext; rfl, by rw [one_smul]; rfl⟩

theorem Descends.algebraMap (Ψ : V →ₗ[ℂ] W) (xbar : W) (r : ℂ) :
    Descends Ψ xbar (algebraMap ℂ (Module.End ℂ V) r) :=
  ⟨r, r • LinearMap.id, by ext v; simp [Module.algebraMap_end_apply], by simp⟩

theorem Descends.add {Ψ : V →ₗ[ℂ] W} {xbar : W} {a b : Module.End ℂ V} (ha : Descends Ψ xbar a)
    (hb : Descends Ψ xbar b) : Descends Ψ xbar (a + b) := by
  obtain ⟨c, abar, h1, h2⟩ := ha
  obtain ⟨d, bbar, h3, h4⟩ := hb
  refine ⟨c + d, abar + bbar, ?_, ?_⟩
  · rw [LinearMap.comp_add, LinearMap.add_comp, h1, h3]
  · rw [LinearMap.add_apply, h2, h4, add_smul]

theorem Descends.mul {Ψ : V →ₗ[ℂ] W} {xbar : W} {a b : Module.End ℂ V} (ha : Descends Ψ xbar a)
    (hb : Descends Ψ xbar b) : Descends Ψ xbar (a * b) := by
  obtain ⟨c, abar, h1, h2⟩ := ha
  obtain ⟨d, bbar, h3, h4⟩ := hb
  refine ⟨c * d, abar ∘ₗ bbar, ?_, ?_⟩
  · rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h1, LinearMap.comp_assoc, h3, LinearMap.comp_assoc]
  · rw [LinearMap.comp_apply, h4, map_smul, h2, smul_smul, mul_comm]

theorem Descends.scalar_unique {Ψ : V →ₗ[ℂ] W} (hΨ : Function.Surjective Ψ) {xbar : W} (hx : xbar ≠ 0)
    {a : Module.End ℂ V} {c d : ℂ} {abar bbar : W →ₗ[ℂ] W}
    (h1 : Ψ ∘ₗ a = abar ∘ₗ Ψ) (h2 : abar xbar = c • xbar) (h3 : Ψ ∘ₗ a = bbar ∘ₗ Ψ) (h4 : bbar xbar = d • xbar) :
    c = d := by
  have hab : abar = bbar := LinearMap.cancel_right hΨ |>.mp (h1.symm.trans h3)
  rw [hab, h4] at h2
  exact (smul_left_injective ℂ hx h2).symm

variable {ι : Type*} (t : ι → Module.End ℂ V)

theorem descends_of_mem_adjoin {Ψ : V →ₗ[ℂ] W} {xbar : W} (ht : ∀ i, Descends Ψ xbar (t i))
    {a : Module.End ℂ V} (ha : a ∈ Algebra.adjoin ℂ (Set.range t)) : Descends Ψ xbar a := by
  refine Algebra.adjoin_induction (p := fun a _ => Descends Ψ xbar a) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩; exact ht i
  · intro r; exact Descends.algebraMap Ψ xbar r
  · intro x y _ _ hx hy; exact hx.add hy
  · intro x y _ _ hx hy; exact hx.mul hy

noncomputable def chiFun {Ψ : V →ₗ[ℂ] W} {xbar : W} (ht : ∀ i, Descends Ψ xbar (t i))
    (a : ↥(Algebra.adjoin ℂ (Set.range t))) : ℂ :=
  (descends_of_mem_adjoin t ht a.2).choose

theorem chiFun_spec {Ψ : V →ₗ[ℂ] W} {xbar : W} (ht : ∀ i, Descends Ψ xbar (t i))
    (a : ↥(Algebra.adjoin ℂ (Set.range t))) :
    ∃ abar : W →ₗ[ℂ] W, Ψ ∘ₗ (a : Module.End ℂ V) = abar ∘ₗ Ψ ∧ abar xbar = chiFun t ht a • xbar :=
  (descends_of_mem_adjoin t ht a.2).choose_spec

theorem chiFun_eq {Ψ : V →ₗ[ℂ] W} (hΨ : Function.Surjective Ψ) {xbar : W} (hx : xbar ≠ 0)
    (ht : ∀ i, Descends Ψ xbar (t i)) (a : ↥(Algebra.adjoin ℂ (Set.range t)))
    {c : ℂ} {abar : W →ₗ[ℂ] W} (h1 : Ψ ∘ₗ (a : Module.End ℂ V) = abar ∘ₗ Ψ) (h2 : abar xbar = c • xbar) :
    chiFun t ht a = c := by
  obtain ⟨bbar, h3, h4⟩ := chiFun_spec t ht a
  exact Descends.scalar_unique hΨ hx h3 h4 h1 h2

noncomputable def chi {Ψ : V →ₗ[ℂ] W} (hΨ : Function.Surjective Ψ) {xbar : W} (hx : xbar ≠ 0)
    (ht : ∀ i, Descends Ψ xbar (t i)) : ↥(Algebra.adjoin ℂ (Set.range t)) →ₐ[ℂ] ℂ where
  toFun := chiFun t ht
  map_one' := by
    obtain ⟨c, abar, h1, h2⟩ := Descends.one Ψ xbar
    have h := chiFun_eq t hΨ hx ht 1 (c := 1) (abar := LinearMap.id) (by ext; rfl) (by rw [one_smul]; rfl)
    exact h
  map_mul' a b := by
    obtain ⟨abar, h1, h2⟩ := chiFun_spec t ht a
    obtain ⟨bbar, h3, h4⟩ := chiFun_spec t ht b
    refine chiFun_eq t hΨ hx ht (a * b) (abar := abar ∘ₗ bbar) ?_ ?_
    · rw [Subalgebra.coe_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h1, LinearMap.comp_assoc, h3,
        LinearMap.comp_assoc]
    · rw [LinearMap.comp_apply, h4, map_smul, h2, smul_smul, mul_comm]
  map_zero' := by
    refine chiFun_eq t hΨ hx ht 0 (abar := 0) ?_ ?_
    · rw [Subalgebra.coe_zero, LinearMap.comp_zero, LinearMap.zero_comp]
    · rw [LinearMap.zero_apply, zero_smul]
  map_add' a b := by
    obtain ⟨abar, h1, h2⟩ := chiFun_spec t ht a
    obtain ⟨bbar, h3, h4⟩ := chiFun_spec t ht b
    refine chiFun_eq t hΨ hx ht (a + b) (abar := abar + bbar) ?_ ?_
    · rw [Subalgebra.coe_add, LinearMap.comp_add, LinearMap.add_comp, h1, h3]
    · rw [LinearMap.add_apply, h2, h4, add_smul]
  commutes' r := by
    refine chiFun_eq t hΨ hx ht _ (abar := r • LinearMap.id) ?_ ?_
    · rw [Subalgebra.coe_algebraMap]
      ext v
      simp [Module.algebraMap_end_apply]
    · simp

theorem chi_apply_gen {Ψ : V →ₗ[ℂ] W} (hΨ : Function.Surjective Ψ) {xbar : W} (hx : xbar ≠ 0)
    (ht : ∀ i, Descends Ψ xbar (t i)) (i : ι) {c : ℂ} {abar : W →ₗ[ℂ] W}
    (h1 : Ψ ∘ₗ t i = abar ∘ₗ Ψ) (h2 : abar xbar = c • xbar) :
    chi t hΨ hx ht ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = c :=
  chiFun_eq t hΨ hx ht _ h1 h2

open scoped IsMulCommutative in

theorem exists_eigenvector_of_quotient [FiniteDimensional ℂ V] (hcomm : ∀ i j, Commute (t i) (t j))
    {Ψ : V →ₗ[ℂ] W} (hΨ : Function.Surjective Ψ) {xbar : W} (hx : xbar ≠ 0) (c : ι → ℂ)
    (Tbar : ι → (W →ₗ[ℂ] W)) (hT : ∀ i, Ψ ∘ₗ t i = Tbar i ∘ₗ Ψ) (heig : ∀ i, Tbar i xbar = c i • xbar) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, t i v = c i • v := by
  have ht : ∀ i, Descends Ψ xbar (t i) := fun i => ⟨c i, Tbar i, hT i, heig i⟩
  haveI : IsMulCommutative ↥(Algebra.adjoin ℂ (Set.range t)) := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (hcomm i j).eq)
  letI : CommRing ↥(Algebra.adjoin ℂ (Set.range t)) := inferInstance
  obtain ⟨v, hv0, hv⟩ :=
    Module.exists_ne_zero_forall_smul_eq_smul_of_algHom (V := V) (chi t hΨ hx ht)
  refine ⟨v, hv0, fun i => ?_⟩
  have h := hv ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  rw [chi_apply_gen t hΨ hx ht i (hT i) (heig i)] at h
  exact h

end Lift

section Main

variable (N : ℕ) [NeZero N] (n : ℕ)

def GoodPrime (S₀ : Set ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀}

theorem main (S₀ : Set ℕ) (Λ : ℕ → ℂ) (x : coeffH1 (ρC N n))
    (hx : x ∉ LinearMap.range (coeffH1parToH1 (ρC N n)))
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∃ T : coeffH1 (ρC N n) →ₗ[ℂ] coeffH1 (ρC N n),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         IsCoeffHeckeOnH1 N ℓ (ρC N n) (binaryFormAlphaAdj ℂ n ℓ) T) ∧
        T x - Λ ℓ • x ∈ LinearMap.range (coeffH1parToH1 (ρC N n))) :
    ∃ f : ModularForm (Gamma0 N) ((n : ℤ) + 2), f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f := by

  set xbar : Q N n := (Rpar N n).mkQ x with hxbar
  have hx0 : xbar ≠ 0 := by
    intro h
    rw [hxbar, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact hx h
  have heigQ : ∀ i : GoodPrime N S₀, TQ N n i.2.1 xbar = Λ i.1 • xbar := by
    rintro ⟨ℓ, hℓ, hℓN, hℓS⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
    rw [unique_of_isCoeffHeckeOnH1 hT (isCoeffHeckeOnH1_TH N n hℓ)] at hTx
    change TQ N n hℓ ((Rpar N n).mkQ x) = Λ ℓ • (Rpar N n).mkQ x
    rw [TQ_mkQ, ← sub_eq_zero, ← map_smul, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hTx

  haveI : FiniteDimensional ℂ (MF N n) := ModularForm.finiteDimensional_Gamma0 N ((n : ℤ) + 2)
  let t : GoodPrime N S₀ → Module.End ℂ (MF N n) := fun i => ModularForm.heckeTLin ((n : ℤ) + 2) i.2.1 i.2.2.1
  have hcomm : ∀ i j, Commute (t i) (t j) := fun i j =>
    ModularForm.heckeTLin_comm ((n : ℤ) + 2) i.2.1 i.2.2.1 j.2.1 j.2.2.1
  obtain ⟨f, hf0, hf⟩ := exists_eigenvector_of_quotient t hcomm (Ψ_surjective N n) hx0 (fun i => Λ i.1)
    (fun i => TQ N n i.2.1) (fun i => LinearMap.ext fun g => (TQ_Ψ N n i.2.1 i.2.2.1 g).symm) heigQ
  refine ⟨f, hf0, fun ℓ hℓ hℓN hℓS => ?_⟩
  exact hf ⟨ℓ, hℓ, hℓN, hℓS⟩

end Main

end A2W1E
p2m_reactivate "P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1.A2W1E"

theorem solution
    (N : ℕ) [NeZero N] (n : ℕ) (S₀ : Set ℕ) (Λ : ℕ → ℂ)
    (x : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : x ∉ LinearMap.range (HeckeEis.coeffH1parToH1
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)))
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∃ T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[ℂ] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         HeckeEis.IsCoeffHeckeOnH1 N ℓ
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) T) ∧
        T x - Λ ℓ • x ∈ LinearMap.range (HeckeEis.coeffH1parToH1
          ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2), f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
        ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = Λ ℓ • f :=
  A2W1E.main N n S₀ Λ x hx heig

end S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1
end P2MW
export P2MW.S_HeckeEis_exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1 (solution)

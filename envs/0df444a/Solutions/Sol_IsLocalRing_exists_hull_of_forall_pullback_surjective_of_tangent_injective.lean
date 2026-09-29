-- Prove2me | solution 1 for IsLocalRing.exists_hull_of_forall_pullback_surjective_of_tangent_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/87845c42-5994-50e5-a73b-7b2386cc6b46

import Mathlib
import Theorems.Thm_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
import Theorems.Thm_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
import Theorems.Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
import Theorems.Thm_IsAdicComplete_of_isNilpotent
import Theorems.Thm_IsLocalRing_isAdicComplete_map_maximalIdeal_quotient
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_MvPowerSeries_algHom_ext_of_apply_X_mem
import Theorems.Thm_MvPowerSeries_isAdicComplete_maximalIdeal
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace P2mSchlessingerHull

open IsLocalRing

structure Datum (O : Type u) [CommRing O] [IsLocalRing O] where
  F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u
  Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
    F A resA → F A resA → Prop
  hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x : F A resA), Frel x x
  hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x y : F A resA), Frel x y → Frel y x
  htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x y z : F A resA), Frel x y → Frel y z → Frel x z
  Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA'
  Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
    Frel x y → Frel (Fmap f hf x) (Fmap f hf y)
  Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x
  Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
    (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
    (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
    (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x))
  x₀ : F (ResidueField O) (RingHom.id (ResidueField O))
  hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀
  hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
      (resB : B →+* ResidueField O), Function.Surjective resB →
      resB.comp (algebraMap O B) = residue O →
    ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
      (resA' : A' →+* ResidueField O), Function.Surjective resA' →
      resA'.comp (algebraMap O A') = residue O →
    ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
      (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
      resA''.comp (algebraMap O A'') = residue O →
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
      (resA : A →+* ResidueField O), Function.Surjective resA →
      resA.comp (algebraMap O A) = residue O →
    ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
      (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
      (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
      (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
      q'.comp p' = q''.comp p'' →
      (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
      Function.Surjective q'' →
      ∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
        ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x''
  r : ℕ
  e : F (DualNumber (ResidueField O))
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom → (Fin r → ResidueField O)
  he_rel : ∀ x y, Frel x y → e x = e y
  he_inj : ∀ x y, e x = e y → Frel x y
  he_smul : ∀ (c : ResidueField O)
      (μ : DualNumber (ResidueField O) →ₐ[O] DualNumber (ResidueField O))
      (hμ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp μ.toRingHom =
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
      (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
      ∀ x, e (Fmap μ hμ x) = c • e x
  he_add : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
      (resB : B →+* ResidueField O), Function.Surjective resB →
      resB.comp (algebraMap O B) = residue O →
      ∀ (p₁ p₂ σ : B →ₐ[O] DualNumber (ResidueField O))
        (hp₁ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          p₁.toRingHom = resB)
        (hp₂ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          p₂.toRingHom = resB)
        (hσ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          σ.toRingHom = resB),
      (∀ b₁ b₂ : B, p₁ b₁ = p₁ b₂ → p₂ b₁ = p₂ b₂ → b₁ = b₂) →
      (∀ t₁ t₂ : DualNumber (ResidueField O), TrivSqZeroExt.fst t₁ = TrivSqZeroExt.fst t₂ →
          ∃ b : B, p₁ b = t₁ ∧ p₂ b = t₂) →
      (∀ b : B, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
      ∀ y : F B resB, e (Fmap σ hσ y) = e (Fmap p₁ hp₁ y) + e (Fmap p₂ hp₂ y)

variable {O : Type u} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  (S : Datum O)

namespace Datum

theorem Fmap_congr {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f f' : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (hf' : resA'.comp f'.toRingHom = resA)
    (h : f = f') (x : S.F A resA) : S.Fmap f hf x = S.Fmap f' hf' x := by
  subst h; rfl

theorem Fmap_comp' {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
    (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
    (hg : resA''.comp g.toRingHom = resA') (h : A →ₐ[O] A'') (hh : resA''.comp h.toRingHom = resA)
    (hgf : g.comp f = h) (x : S.F A resA) : S.Frel (S.Fmap h hh x) (S.Fmap g hg (S.Fmap f hf x)) := by
  subst hgf; exact S.Fmap_comp f g hf hg hh x

theorem Fmap_gf_id {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (g : A' →ₐ[O] A)
    (hg : resA.comp g.toRingHom = resA') (hgf : g.comp f = AlgHom.id O A) (z : S.F A resA) :
    S.Frel (S.Fmap g hg (S.Fmap f hf z)) z := by
  have hc : resA.comp (g.comp f).toRingHom = resA := by rw [hgf]; rfl
  have h1 := S.Fmap_comp f g hf hg hc z
  have h2 : S.Frel (S.Fmap (g.comp f) hc z) z := by
    rw [S.Fmap_congr (g.comp f) (AlgHom.id O A) hc rfl hgf z]
    exact S.Fmap_id rfl z
  exact S.htrans _ _ _ (S.hsymm _ _ h1) h2

theorem comp_compat {T : Type u} [CommRing T] [Algebra O T] {resT : T →+* ResidueField O}
    {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (u : T →ₐ[O] A)
    (hu : resA.comp u.toRingHom = resT) : resA'.comp (f.comp u).toRingHom = resT := by
  rw [← hu, ← hf]; rfl
end Datum

theorem ker_res_eq_maximalIdeal {B : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (res : B →+* ResidueField O) : RingHom.ker res = maximalIdeal B :=
  IsLocalRing.eq_maximalIdeal
    ((IsArtinianRing.isPrime_iff_isMaximal (RingHom.ker res)).1 (RingHom.ker_isPrime res))

theorem isUnit_iff_res_ne_zero {B : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (res : B →+* ResidueField O) (b : B) : IsUnit b ↔ res b ≠ 0 := by
  rw [ne_eq, ← RingHom.mem_ker, ker_res_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

theorem exists_pow_maximalIdeal_eq_bot (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] :
    ∃ N : ℕ, maximalIdeal B ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 ‹_›
  exact ⟨N, hN⟩

theorem isAdicComplete_of_artinian (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] :
    IsAdicComplete (maximalIdeal B) B :=
  IsAdicComplete.of_isNilpotent ((isArtinianRing_iff_isNilpotent_maximalIdeal B).1 ‹_›)

theorem isHausdorff_of_artinian (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  haveI := isAdicComplete_of_artinian B
  inferInstance

section powerseries

variable (O) (d : ℕ)

abbrev PS : Type u := MvPowerSeries (Fin d) O

scoped instance : IsNoetherianRing (PS O d) := MvPowerSeries.isNoetherianRing_of_finite

scoped instance : IsAdicComplete (maximalIdeal (PS O d)) (PS O d) := MvPowerSeries.isAdicComplete_maximalIdeal

def resS : PS O d →+* ResidueField O := (residue O).comp (MvPowerSeries.constantCoeff (σ := Fin d) (R := O))

theorem resS_apply (f : PS O d) : resS O d f = residue O (MvPowerSeries.constantCoeff f) := rfl

theorem resS_compat : (resS O d).comp (algebraMap O (PS O d)) = residue O := by
  ext o; change residue O (MvPowerSeries.constantCoeff (MvPowerSeries.C o)) = _
  rw [MvPowerSeries.constantCoeff_C]

theorem resS_X (i : Fin d) : resS O d (MvPowerSeries.X i) = 0 := by
  rw [resS_apply, MvPowerSeries.constantCoeff_X, map_zero]

theorem ker_resS : RingHom.ker (resS O d) = maximalIdeal (PS O d) := by
  ext f
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    resS_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem resS_surjective : Function.Surjective (resS O d) := fun c => by
  obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
  exact ⟨algebraMap O _ o, by rw [← RingHom.comp_apply, resS_compat]⟩
end powerseries

section tangentring

variable (O) (d : ℕ)

abbrev Vd : Type u := Fin d → ResidueField O
abbrev Td : Type u := TrivSqZeroExt (ResidueField O) (Vd O d)
abbrev Dk : Type u := DualNumber (ResidueField O)

abbrev resT : Td O d →+* ResidueField O := (TrivSqZeroExt.fstHom O (ResidueField O) (Vd O d)).toRingHom
abbrev resD : Dk O →+* ResidueField O := (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom

theorem isLocalRing_tsze (M : Type u) [AddCommGroup M] [Module (ResidueField O) M]
    [Module (ResidueField O)ᵐᵒᵖ M] [IsCentralScalar (ResidueField O) M] :
    IsLocalRing (TrivSqZeroExt (ResidueField O) M) := by
  haveI : Nontrivial (TrivSqZeroExt (ResidueField O) M) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg TrivSqZeroExt.fst h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  by_cases h : x.fst = 0
  · right
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, h, sub_zero]
    exact isUnit_one
  · left
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact isUnit_iff_ne_zero.2 h

theorem isArtinianRing_tsze (M : Type u) [AddCommGroup M] [Module (ResidueField O) M]
    [Module (ResidueField O)ᵐᵒᵖ M] [IsCentralScalar (ResidueField O) M] [Module.Finite (ResidueField O) M] :
    IsArtinianRing (TrivSqZeroExt (ResidueField O) M) :=
  haveI : Module.Finite (ResidueField O) (TrivSqZeroExt (ResidueField O) M) :=
    inferInstanceAs (Module.Finite (ResidueField O) (ResidueField O × M))
  IsArtinianRing.of_finite (ResidueField O) _

scoped instance : IsLocalRing (Td O d) := isLocalRing_tsze O _
scoped instance : IsArtinianRing (Td O d) := isArtinianRing_tsze O _
scoped instance : IsArtinianRing (Dk O) := isArtinianRing_tsze O _

theorem ker_resT : RingHom.ker (resT O d) = maximalIdeal (Td O d) := ker_res_eq_maximalIdeal _
theorem ker_resD : RingHom.ker (resD O) = maximalIdeal (Dk O) := ker_res_eq_maximalIdeal _

def θc (c : Fin d → ResidueField O) : Td O d →ₐ[O] Dk O where
  toFun t := ((t.fst, ∑ i, t.snd i * c i) : ResidueField O × ResidueField O)
  map_one' := TrivSqZeroExt.ext rfl (by
    change ∑ i, (1 : Td O d).snd i * c i = 0
    simp)
  map_mul' x y := TrivSqZeroExt.ext rfl (by
    change ∑ i, (x * y).snd i * c i =
      x.fst • (∑ i, y.snd i * c i) + MulOpposite.op y.fst • (∑ i, x.snd i * c i)
    rw [TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring)
  map_zero' := TrivSqZeroExt.ext rfl (by
    change ∑ i, (0 : Td O d).snd i * c i = 0
    simp)
  map_add' x y := TrivSqZeroExt.ext rfl (by
    change ∑ i, (x + y).snd i * c i = (∑ i, x.snd i * c i) + ∑ i, y.snd i * c i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TrivSqZeroExt.snd_add, Pi.add_apply, add_mul])
  commutes' o := TrivSqZeroExt.ext rfl (by
    change ∑ i, (algebraMap O (Td O d) o).snd i * c i = (algebraMap O (Dk O) o).snd
    rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inl]
    simp)

theorem θc_inr_single (c : Fin d → ResidueField O) (i : Fin d) :
    θc O d c (TrivSqZeroExt.inr (Pi.single i 1)) = TrivSqZeroExt.inr (c i) := by
  refine TrivSqZeroExt.ext rfl ?_
  change ∑ j, (Pi.single i (1 : ResidueField O) : Vd O d) j * c j = c i
  simp [Pi.single_apply]
end tangentring

section phi

variable (O) (d : ℕ)

theorem mul_eq_zero_of_fst_eq_zero {M : Type u} [AddCommGroup M] [Module (ResidueField O) M]
    [Module (ResidueField O)ᵐᵒᵖ M] [IsCentralScalar (ResidueField O) M] (x y : TrivSqZeroExt (ResidueField O) M)
    (hx : x.fst = 0) (hy : y.fst = 0) : x * y = 0 :=
  TrivSqZeroExt.ext (by rw [TrivSqZeroExt.fst_mul, hx, zero_mul]; rfl)
    (by rw [TrivSqZeroExt.snd_mul, hx, hy, zero_smul, MulOpposite.op_zero, zero_smul, add_zero]; rfl)

theorem exists_φ : ∃ φ : PS O d →ₐ[O] Td O d, ∀ i, φ (MvPowerSeries.X i) = TrivSqZeroExt.inr (Pi.single i 1) := by
  haveI : IsAdicComplete (maximalIdeal (Td O d)) (Td O d) := isAdicComplete_of_artinian _
  refine MvPowerSeries.exists_algHom_apply_X_eq (maximalIdeal (Td O d)) _ (fun i => ?_)
  rw [← ker_resT, RingHom.mem_ker]; rfl

def φ₂ : PS O d →ₐ[O] Td O d := (exists_φ O d).choose

theorem φ₂_X (i : Fin d) : φ₂ O d (MvPowerSeries.X i) = TrivSqZeroExt.inr (Pi.single i 1) :=
  (exists_φ O d).choose_spec i

def resSₐ : PS O d →ₐ[O] ResidueField O :=
  { resS O d with
    commutes' := fun o => by
      change resS O d (algebraMap O (PS O d) o) = algebraMap O (ResidueField O) o
      rw [← RingHom.comp_apply, resS_compat]; rfl }

theorem φ₂_compat : (resT O d).comp (φ₂ O d).toRingHom = resS O d := by
  have key : (TrivSqZeroExt.fstHom O (ResidueField O) (Vd O d)).comp (φ₂ O d) = resSₐ O d := by
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (⊥ : Ideal (ResidueField O)) _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply, φ₂_X]; exact (Submodule.mem_bot _).2 rfl
    · rw [AlgHom.comp_apply, φ₂_X]
      change (0 : ResidueField O) = resS O d (MvPowerSeries.X i)
      rw [resS_X]
  exact congrArg AlgHom.toRingHom key

theorem resT_φ₂ (f : PS O d) : (φ₂ O d f).fst = resS O d f := by
  rw [← φ₂_compat]; rfl

theorem φ₂_C_mul_X (o' : O) (i : Fin d) :
    φ₂ O d (algebraMap O _ o' * MvPowerSeries.X i) = TrivSqZeroExt.inr (residue O o' • Pi.single i 1) := by
  rw [map_mul, AlgHom.commutes, φ₂_X, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl_mul_inr]; rfl

theorem φ₂_surjective : Function.Surjective (φ₂ O d) := by
  intro t
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective t.fst
  have hv : ∀ i, ∃ oi : O, residue O oi = t.snd i := fun i => IsLocalRing.residue_surjective _
  choose ov hov using hv
  refine ⟨algebraMap O _ o + ∑ i, algebraMap O _ (ov i) * MvPowerSeries.X i, TrivSqZeroExt.ext ?_ ?_⟩
  · rw [resT_φ₂, map_add, map_sum, ← RingHom.comp_apply, resS_compat, ho]
    simp [resS_X]
  · rw [map_add, TrivSqZeroExt.snd_add, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl',
      TrivSqZeroExt.snd_inl, zero_add, map_sum, TrivSqZeroExt.snd_sum]
    simp_rw [φ₂_C_mul_X, TrivSqZeroExt.snd_inr, hov]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]

theorem ker_φ₂_le : RingHom.ker (φ₂ O d) ≤ maximalIdeal (PS O d) := by
  intro x hx
  rw [← ker_resS, RingHom.mem_ker, ← resT_φ₂, RingHom.mem_ker.1 hx]; rfl

theorem sq_le_ker_φ₂ : maximalIdeal (PS O d) ^ 2 ≤ RingHom.ker (φ₂ O d) := by
  rw [pow_two, Ideal.mul_le]
  intro r hr s hs
  rw [← ker_resS] at hr hs
  rw [RingHom.mem_ker, map_mul]
  exact mul_eq_zero_of_fst_eq_zero O _ _ (by rw [resT_φ₂]; exact hr) (by rw [resT_φ₂]; exact hs)
end phi

section adm

variable (O) (d : ℕ)

structure Adm where
  I : Ideal (PS O d)
  le : I ≤ maximalIdeal (PS O d)
  N : ℕ
  pow_le : maximalIdeal (PS O d) ^ N ≤ I

abbrev Q (J : Adm O d) : Type u := PS O d ⧸ J.I

variable {O d}

private theorem _root_.P2mSchlessingerHull.ne_top (J : Adm O d) : J.I ≠ ⊤ := fun h =>
  (IsLocalRing.maximalIdeal.isMaximal (PS O d)).ne_top (top_le_iff.1 (h ▸ J.le))

p2m_export "P2mSchlessingerHull" "ne_top"
scoped instance (J : Adm O d) : Nontrivial (Q O d J) := Ideal.Quotient.nontrivial_iff.2 (ne_top J)

scoped instance (J : Adm O d) : IsLocalRing (Q O d J) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk J.I) Ideal.Quotient.mk_surjective

theorem maximalIdeal_quotient (J : Ideal (PS O d)) (hJ : J ≤ maximalIdeal (PS O d))
    [IsLocalRing (PS O d ⧸ J)] : maximalIdeal (PS O d ⧸ J) = (maximalIdeal (PS O d)).map (Ideal.Quotient.mk J) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun ha => hx (ha.map _)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨v, hv⟩
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑v⁻¹ : PS O d ⧸ J)
    have h1 : Ideal.Quotient.mk J (a * b) = 1 := by rw [map_mul, hb, ← hv, Units.mul_inv]
    have h2 : a * b - 1 ∈ J := by rw [← Ideal.Quotient.eq, h1, map_one]
    have h3 : (1 : PS O d) ∈ maximalIdeal (PS O d) := by
      have := (maximalIdeal (PS O d)).sub_mem (Ideal.mul_mem_right b _ ha) (hJ h2)
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h3)

scoped instance (J : Adm O d) : IsArtinianRing (Q O d J) :=
  (isArtinianRing_iff_isNilpotent_maximalIdeal _).2 ⟨J.N, by
    rw [maximalIdeal_quotient J.I J.le, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]
    exact J.pow_le⟩

variable (O d) in
def resQ (J : Adm O d) : Q O d J →+* ResidueField O :=
  Ideal.Quotient.lift J.I (resS O d) fun a ha => by
    have := J.le ha; rwa [← ker_resS] at this

theorem resQ_mk (J : Adm O d) (a : PS O d) : resQ O d J (Ideal.Quotient.mk J.I a) = resS O d a := rfl

theorem resQ_surjective (J : Adm O d) : Function.Surjective (resQ O d J) := fun c => by
  obtain ⟨a, rfl⟩ := resS_surjective O d c
  exact ⟨Ideal.Quotient.mk J.I a, rfl⟩

theorem resQ_compat (J : Adm O d) : (resQ O d J).comp (algebraMap O (Q O d J)) = residue O := by
  rw [← resS_compat O d]; rfl

theorem ker_resQ (J : Adm O d) : RingHom.ker (resQ O d J) = maximalIdeal (Q O d J) := ker_res_eq_maximalIdeal _

abbrev fac {K J : Adm O d} (h : K.I ≤ J.I) : Q O d K →ₐ[O] Q O d J := Ideal.Quotient.factorₐ O h

theorem fac_mk {K J : Adm O d} (h : K.I ≤ J.I) (a : PS O d) :
    fac h (Ideal.Quotient.mk K.I a) = Ideal.Quotient.mk J.I a := rfl

theorem fac_comp_mkₐ {K J : Adm O d} (h : K.I ≤ J.I) :
    (fac h).comp (Ideal.Quotient.mkₐ O K.I) = Ideal.Quotient.mkₐ O J.I := AlgHom.ext fun _ => rfl

theorem fac_compat {K J : Adm O d} (h : K.I ≤ J.I) : (resQ O d J).comp (fac h).toRingHom = resQ O d K :=
  RingHom.ext fun x => Quotient.inductionOn' x fun _ => rfl

theorem fac_comp_fac {K J L : Adm O d} (h₁ : K.I ≤ J.I) (h₂ : J.I ≤ L.I) :
    (fac h₂).comp (fac h₁) = fac (h₁.trans h₂) :=
  Ideal.Quotient.algHom_ext O (AlgHom.ext fun _ => rfl)

theorem fac_refl (K : Adm O d) : fac (le_refl K.I) = AlgHom.id O (Q O d K) :=
  Ideal.Quotient.algHom_ext O (AlgHom.ext fun _ => rfl)

theorem fac_surjective {K J : Adm O d} (h : K.I ≤ J.I) : Function.Surjective (fac h) := fun x => by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk K.I a, rfl⟩

variable (O d) in
theorem exists_compl (J K₁ K₂ : Ideal (PS O d)) (hmK₁ : maximalIdeal (PS O d) * J ≤ K₁) (hK₁ : K₁ ≤ J)
    (hK₂ : K₂ ≤ J) : ∃ K₁' : Ideal (PS O d), K₁ ≤ K₁' ∧ K₁' ≤ J ∧ K₁' ⊓ K₂ = K₁ ⊓ K₂ ∧ K₁' ⊔ K₂ = J := by
  let 𝒞 : Set (Ideal (PS O d)) := {C | K₁ ≤ C ∧ C ≤ J ∧ C ⊓ K₂ = K₁ ⊓ K₂}
  obtain ⟨C, ⟨hC₁, hC₂, hC₃⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (PS O d) (PS O d)) 𝒞 ⟨K₁, le_rfl, hK₁, rfl⟩
  refine ⟨C, hC₁, hC₂, hC₃, le_antisymm (sup_le hC₂ hK₂) fun x hx => ?_⟩
  by_contra hxC
  let C' : Ideal (PS O d) := C ⊔ Ideal.span {x}
  have hC' : C' ∈ 𝒞 := by
    refine ⟨hC₁.trans le_sup_left, sup_le hC₂ ((Ideal.span_singleton_le_iff_mem _).2 hx), ?_⟩
    apply le_antisymm _ (hC₃ ▸ inf_le_inf_right K₂ le_sup_left)
    rintro y ⟨hy₁, hy₂⟩
    change y ∈ C ⊔ Ideal.span {x} at hy₁
    obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.1 hy₁
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    by_cases hs : IsUnit s
    · exfalso; apply hxC
      have : x = ↑hs.unit⁻¹ * ((c + s * x) - c) := by
        rw [add_sub_cancel_left, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.mem_sup_right hy₂) (Ideal.mem_sup_left hc))
    · have hsx : s * x ∈ C :=
        hC₁ (hmK₁ (Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).2 hs) hx))
      rw [← hC₃]
      exact ⟨C.add_mem hc hsx, hy₂⟩
  have hle : C ≤ C' := le_sup_left
  have heq : C = C' := by
    by_contra hne
    exact hmax C' hC' (lt_of_le_of_ne hle hne)
  apply hxC
  have : x ∈ C' := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  rw [← heq] at this
  exact Ideal.mem_sup_left this
end adm

namespace Datum

variable (d : ℕ)

structure Stage where
  J : Adm O d
  ξ : S.F (Q O d J) (resQ O d J)

variable {S d}

def sub (s : Stage S d) (K : Ideal (PS O d)) (h : maximalIdeal (PS O d) * s.J.I ≤ K ∧ K ≤ s.J.I) : Adm O d :=
  ⟨K, h.2.trans s.J.le, s.J.N + 1, by
    rw [pow_succ']; exact (Ideal.mul_mono_right s.J.pow_le).trans h.1⟩

def Admissible (s : Stage S d) (K : Ideal (PS O d)) : Prop :=
  ∃ (h : maximalIdeal (PS O d) * s.J.I ≤ K ∧ K ≤ s.J.I),
    ∃ ζ : S.F (Q O d (sub s K h)) (resQ O d (sub s K h)),
      S.Frel (S.Fmap (fac (K := sub s K h) (J := s.J) h.2) (fac_compat _) ζ) s.ξ

theorem adm_self (s : Stage S d) : Admissible s s.J.I := by
  have h : maximalIdeal (PS O d) * s.J.I ≤ s.J.I ∧ s.J.I ≤ s.J.I := ⟨Ideal.mul_le_right, le_rfl⟩
  refine ⟨h, ?_⟩
  let K : Adm O d := sub s s.J.I h
  have e1 : K.I ≤ s.J.I := le_rfl
  have e2 : s.J.I ≤ K.I := le_rfl
  refine ⟨S.Fmap (fac (K := s.J) (J := K) e2) (fac_compat e2) s.ξ, ?_⟩
  exact S.Fmap_gf_id (fac (K := s.J) (J := K) e2) (fac_compat e2) (fac (K := K) (J := s.J) e1)
    (fac_compat e1) ((fac_comp_fac e2 e1).trans (fac_refl s.J)) s.ξ

theorem adm_mono (s : Stage S d) {K K' : Ideal (PS O d)} (hK : Admissible s K) (h₁ : K ≤ K') (h₂ : K' ≤ s.J.I) :
    Admissible s K' := by
  obtain ⟨⟨hmK, hKJ⟩, ζ, hζ⟩ := hK
  refine ⟨⟨hmK.trans h₁, h₂⟩, S.Fmap (fac (K := sub s K ⟨hmK, hKJ⟩) (J := sub s K' ⟨hmK.trans h₁, h₂⟩) h₁)
    (fac_compat _) ζ, ?_⟩
  refine S.htrans _ _ _ (S.hsymm _ _ (S.Fmap_comp' _ _ _ _ _ (fac_compat _) (fac_comp_fac _ _) ζ)) hζ

theorem adm_inf (s : Stage S d) {K₁ K₂ : Ideal (PS O d)} (h₁ : Admissible s K₁) (h₂ : Admissible s K₂) :
    Admissible s (K₁ ⊓ K₂) := by
  obtain ⟨⟨hmK₁, hK₁J⟩, ζ₁, hζ₁⟩ := h₁
  obtain ⟨⟨hmK₂, hK₂J⟩, ζ₂, hζ₂⟩ := h₂
  obtain ⟨K₁', hK₁K₁', hK₁'J, hinf, hsup⟩ := exists_compl O d s.J.I K₁ K₂ hmK₁ hK₁J hK₂J

  let A₁ : Adm O d := sub s K₁' ⟨hmK₁.trans hK₁K₁', hK₁'J⟩
  let A₂ : Adm O d := sub s K₂ ⟨hmK₂, hK₂J⟩
  have hB : maximalIdeal (PS O d) * s.J.I ≤ K₁' ⊓ K₂ ∧ K₁' ⊓ K₂ ≤ s.J.I :=
    ⟨le_inf (hmK₁.trans hK₁K₁') hmK₂, inf_le_left.trans hK₁'J⟩
  let B : Adm O d := sub s (K₁' ⊓ K₂) hB
  have hp' : B.I ≤ A₁.I := inf_le_left
  have hp'' : B.I ≤ A₂.I := inf_le_right

  have hcart : ∀ (a' : Q O d A₁) (a'' : Q O d A₂), fac (K := A₁) (J := s.J) hK₁'J a' =
      fac (K := A₂) (J := s.J) hK₂J a'' → ∃! b : Q O d B, fac hp' b = a' ∧ fac hp'' b = a'' := by
    intro a' a'' h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a''
    rw [fac_mk, fac_mk, Ideal.Quotient.eq] at h
    have hxy : x - y ∈ K₁' ⊔ K₂ := by rw [hsup]; exact h
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hxy
    refine ⟨Ideal.Quotient.mk B.I (x - u), ⟨?_, ?_⟩, ?_⟩
    · rw [fac_mk, Ideal.Quotient.eq]; change x - u - x ∈ K₁'
      rw [sub_sub_cancel_left]; exact K₁'.neg_mem hu
    · rw [fac_mk, Ideal.Quotient.eq]; change x - u - y ∈ K₂
      have : x - u - y = v := by rw [sub_right_comm, ← huv, add_sub_cancel_left]
      rw [this]; exact hv
    · rintro b ⟨hb₁, hb₂⟩
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [fac_mk, Ideal.Quotient.eq] at hb₁ hb₂
      rw [Ideal.Quotient.eq]
      change w - (x - u) ∈ K₁' ⊓ K₂
      refine ⟨?_, ?_⟩
      · change w - (x - u) ∈ K₁'
        have : w - (x - u) = (w - x) + u := by ring
        rw [this]; exact K₁'.add_mem hb₁ hu
      · change w - (x - u) ∈ K₂
        have : w - (x - u) = (w - y) - v := by
          have := huv; linear_combination this
        rw [this]; exact K₂.sub_mem hb₂ hv

  let ζ₁' : S.F (Q O d A₁) (resQ O d A₁) :=
    S.Fmap (fac (K := sub s K₁ ⟨hmK₁, hK₁J⟩) (J := A₁) hK₁K₁') (fac_compat _) ζ₁
  have hζ₁' : S.Frel (S.Fmap (fac (K := A₁) (J := s.J) hK₁'J) (fac_compat _) ζ₁') s.ξ :=
    S.htrans _ _ _ (S.hsymm _ _ (S.Fmap_comp' _ _ _ _ _ (fac_compat _) (fac_comp_fac _ _) ζ₁)) hζ₁
  obtain ⟨y, hy₁, hy₂⟩ := S.hglue (Q O d B) (resQ O d B) (resQ_surjective B) (resQ_compat B)
    (Q O d A₁) (resQ O d A₁) (resQ_surjective A₁) (resQ_compat A₁)
    (Q O d A₂) (resQ O d A₂) (resQ_surjective A₂) (resQ_compat A₂)
    (Q O d s.J) (resQ O d s.J) (resQ_surjective s.J) (resQ_compat s.J)
    (fac hp') (fac_compat _) (fac hp'') (fac_compat _) (fac hK₁'J) (fac_compat _) (fac hK₂J) (fac_compat _)
    (by rw [fac_comp_fac, fac_comp_fac]) hcart (fac_surjective _) ζ₁' ζ₂
    (S.htrans _ _ _ hζ₁' (S.hsymm _ _ hζ₂))

  have hK : maximalIdeal (PS O d) * s.J.I ≤ K₁ ⊓ K₂ ∧ K₁ ⊓ K₂ ≤ s.J.I :=
    ⟨le_inf hmK₁ hmK₂, inf_le_left.trans hK₁J⟩
  have hBK : B.I ≤ (sub s (K₁ ⊓ K₂) hK).I := le_of_eq hinf
  refine ⟨hK, S.Fmap (fac hBK) (fac_compat _) y, ?_⟩
  refine S.htrans _ _ _ (S.hsymm _ _ (S.Fmap_comp' _ _ _ _ _ (fac_compat _) (fac_comp_fac _ _) y)) ?_
  refine S.htrans _ _ _ (S.Fmap_comp' (fac hp') (fac hK₁'J) (fac_compat _) (fac_compat _) _ (fac_compat _)
    (fac_comp_fac _ _) y) ?_
  exact S.htrans _ _ _ (S.Fmap_rel _ _ _ _ hy₁) hζ₁'

theorem exists_least (s : Stage S d) : ∃ K₀, Admissible s K₀ ∧ ∀ K, Admissible s K → K₀ ≤ K := by
  let L : Adm O d := sub s (maximalIdeal (PS O d) * s.J.I) ⟨le_rfl, Ideal.mul_le_right⟩
  let 𝒩 : Set (Ideal (Q O d L)) := {N | ∃ K, Admissible s K ∧ K.map (Ideal.Quotient.mk L.I) = N}
  obtain ⟨_, ⟨K₀, hK₀, rfl⟩, hmin⟩ :=
    IsArtinian.set_has_minimal (R := Q O d L) (M := Q O d L) 𝒩 ⟨_, s.J.I, adm_self s, rfl⟩
  refine ⟨K₀, hK₀, fun K hK => ?_⟩
  have hinf := adm_inf s hK₀ hK
  have hle : (K₀ ⊓ K).map (Ideal.Quotient.mk L.I) ≤ K₀.map (Ideal.Quotient.mk L.I) := Ideal.map_mono inf_le_left
  have heq : (K₀ ⊓ K).map (Ideal.Quotient.mk L.I) = K₀.map (Ideal.Quotient.mk L.I) := by
    by_contra hne
    exact hmin _ ⟨_, hinf, rfl⟩ (lt_of_le_of_ne hle hne)
  have key : ∀ K', Admissible s K' → (K'.map (Ideal.Quotient.mk L.I)).comap (Ideal.Quotient.mk L.I) = K' := by
    intro K' ⟨⟨hmK', _⟩, _⟩
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.2 hmK'
  have h2 : K₀ ⊓ K = K₀ := by rw [← key _ hinf, heq, key _ hK₀]
  exact inf_eq_left.1 h2

def step (s : Stage S d) : Stage S d :=
  ⟨sub s (exists_least s).choose (exists_least s).choose_spec.1.choose,
    (exists_least s).choose_spec.1.choose_spec.choose⟩

theorem step_le (s : Stage S d) : (step s).J.I ≤ s.J.I := (exists_least s).choose_spec.1.choose.2

theorem step_lift (s : Stage S d) :
    S.Frel (S.Fmap (fac (K := (step s).J) (J := s.J) (step_le s)) (fac_compat _) (step s).ξ) s.ξ :=
  (exists_least s).choose_spec.1.choose_spec.choose_spec

theorem step_least (s : Stage S d) (K : Ideal (PS O d)) (hK : Admissible s K) : (step s).J.I ≤ K :=
  (exists_least s).choose_spec.2 K hK

def stage (s₀ : Stage S d) : ℕ → Stage S d
  | 0 => s₀
  | q + 1 => step (stage s₀ q)

theorem stage_antitone (s₀ : Stage S d) : Antitone fun q => (stage s₀ q).J.I :=
  antitone_nat_of_succ_le fun q => step_le _

theorem stage_le (s₀ : Stage S d) {q q' : ℕ} (h : q ≤ q') : (stage s₀ q').J.I ≤ (stage s₀ q).J.I :=
  stage_antitone s₀ h

theorem stage_lift (s₀ : Stage S d) (q : ℕ) : ∀ (n : ℕ),
    S.Frel (S.Fmap (fac (K := (stage s₀ (q + n)).J) (J := (stage s₀ q).J) (stage_le s₀ (Nat.le_add_right q n)))
      (fac_compat _) (stage s₀ (q + n)).ξ) (stage s₀ q).ξ
  | 0 => by
    rw [S.Fmap_congr _ (AlgHom.id O _) (fac_compat _) rfl (fac_refl _)]
    exact S.Fmap_id rfl _
  | n + 1 => by
    have h1 := step_lift (stage s₀ (q + n))
    have h2 := stage_lift s₀ q n
    have h3 := S.Fmap_comp' (fac (K := (stage s₀ (q + n + 1)).J) (J := (stage s₀ (q + n)).J) (step_le _))
      (fac (K := (stage s₀ (q + n)).J) (J := (stage s₀ q).J) (stage_le s₀ (Nat.le_add_right q n)))
      (fac_compat _) (fac_compat _) _ (fac_compat _) (fac_comp_fac _ _) (stage s₀ (q + n + 1)).ξ
    exact S.htrans _ _ _ h3 (S.htrans _ _ _ (S.Fmap_rel _ _ _ _ h1) h2)

theorem stage_lift' (s₀ : Stage S d) {q q' : ℕ} (h : q ≤ q') :
    S.Frel (S.Fmap (fac (K := (stage s₀ q').J) (J := (stage s₀ q).J) (stage_le s₀ h)) (fac_compat _)
      (stage s₀ q').ξ) (stage s₀ q).ξ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  exact stage_lift s₀ q n

variable (S)

theorem exists_first : ∃ (d : ℕ) (ξ : S.F (Td O d) (resT O d)),
    (∀ x : S.F (Dk O) (resD O), ∃ (θ : Td O d →ₐ[O] Dk O) (hθ : (resD O).comp θ.toRingHom = resT O d),
      S.Frel (S.Fmap θ hθ ξ) x) ∧
    (∀ (θ θ' : Td O d →ₐ[O] Dk O) (hθ : (resD O).comp θ.toRingHom = resT O d)
      (hθ' : (resD O).comp θ'.toRingHom = resT O d), S.Frel (S.Fmap θ hθ ξ) (S.Fmap θ' hθ' ξ) → θ = θ') :=
  IsLocalRing.exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
    O S.F S.Frel S.hrefl S.hsymm S.htrans S.Fmap S.Fmap_rel S.Fmap_id S.Fmap_comp S.x₀ S.hx₀ S.hglue S.r S.e
    S.he_rel S.he_inj S.he_smul S.he_add

def dm : ℕ := (exists_first S).choose

def ξ₂ : S.F (Td O S.dm) (resT O S.dm) := (exists_first S).choose_spec.choose

theorem ξ₂_surj (x : S.F (Dk O) (resD O)) : ∃ (θ : Td O S.dm →ₐ[O] Dk O)
    (hθ : (resD O).comp θ.toRingHom = resT O S.dm), S.Frel (S.Fmap θ hθ S.ξ₂) x :=
  (exists_first S).choose_spec.choose_spec.1 x

theorem ξ₂_inj (θ θ' : Td O S.dm →ₐ[O] Dk O) (hθ : (resD O).comp θ.toRingHom = resT O S.dm)
    (hθ' : (resD O).comp θ'.toRingHom = resT O S.dm) (h : S.Frel (S.Fmap θ hθ S.ξ₂) (S.Fmap θ' hθ' S.ξ₂)) :
    θ = θ' :=
  (exists_first S).choose_spec.choose_spec.2 θ θ' hθ hθ' h

def J₂ : Adm O S.dm :=
  ⟨RingHom.ker (φ₂ O S.dm).toRingHom, ker_φ₂_le O S.dm, 2, sq_le_ker_φ₂ O S.dm⟩

def e₂ : Q O S.dm S.J₂ ≃ₐ[O] Td O S.dm := Ideal.quotientKerAlgEquivOfSurjective (φ₂_surjective O S.dm)

theorem e₂_mk (a : PS O S.dm) : S.e₂ (Ideal.Quotient.mk S.J₂.I a) = φ₂ O S.dm a :=
  (Ideal.quotientKerAlgEquivOfSurjective_apply (φ₂_surjective O S.dm) _).trans (RingHom.kerLift_mk _ _)

theorem e₂_compat : (resT O S.dm).comp (S.e₂ : Q O S.dm S.J₂ →ₐ[O] Td O S.dm).toRingHom = resQ O S.dm S.J₂ := by
  refine RingHom.ext fun x => Quotient.inductionOn' x fun a => ?_
  change resT O S.dm (S.e₂ (Ideal.Quotient.mk S.J₂.I a)) = resS O S.dm a
  rw [e₂_mk, ← resT_φ₂]
  rfl

theorem e₂_symm_compat :
    (resQ O S.dm S.J₂).comp (S.e₂.symm : Td O S.dm →ₐ[O] Q O S.dm S.J₂).toRingHom = resT O S.dm := by
  rw [← e₂_compat]
  refine RingHom.ext fun t => ?_
  change resT O S.dm (S.e₂ (S.e₂.symm t)) = resT O S.dm t
  rw [AlgEquiv.apply_symm_apply]

def s₀ : Stage S S.dm := ⟨S.J₂, S.Fmap (S.e₂.symm : Td O S.dm →ₐ[O] Q O S.dm S.J₂) S.e₂_symm_compat S.ξ₂⟩

abbrev st (q : ℕ) : Stage S S.dm := stage S.s₀ q

def Jinf : Ideal (PS O S.dm) := ⨅ q, (S.st q).J.I

theorem Jinf_le (q : ℕ) : S.Jinf ≤ (S.st q).J.I := iInf_le _ q

theorem Jinf_le_max : S.Jinf ≤ maximalIdeal (PS O S.dm) := (S.Jinf_le 0).trans (S.st 0).J.le

abbrev Rh : Type u := PS O S.dm ⧸ S.Jinf

scoped instance : Nontrivial S.Rh := Ideal.Quotient.nontrivial_iff.2 fun h =>
  (IsLocalRing.maximalIdeal.isMaximal (PS O S.dm)).ne_top (top_le_iff.1 (h ▸ S.Jinf_le_max))

scoped instance : IsLocalRing S.Rh := IsLocalRing.of_surjective' (Ideal.Quotient.mk S.Jinf) Ideal.Quotient.mk_surjective

theorem maximalIdeal_Rh : maximalIdeal S.Rh = (maximalIdeal (PS O S.dm)).map (Ideal.Quotient.mk S.Jinf) :=
  maximalIdeal_quotient S.Jinf S.Jinf_le_max

scoped instance : IsAdicComplete (maximalIdeal S.Rh) S.Rh := by
  rw [maximalIdeal_Rh]; exact IsLocalRing.isAdicComplete_map_maximalIdeal_quotient S.Jinf

def resR : S.Rh →+* ResidueField O :=
  Ideal.Quotient.lift S.Jinf (resS O S.dm) fun a ha => by
    have := S.Jinf_le_max ha; rwa [← ker_resS] at this

theorem resR_mk (a : PS O S.dm) : S.resR (Ideal.Quotient.mk S.Jinf a) = resS O S.dm a := rfl

theorem resR_compat : S.resR.comp (algebraMap O S.Rh) = residue O := by rw [← resS_compat O S.dm]; rfl

abbrev facR (q : ℕ) : S.Rh →ₐ[O] Q O S.dm (S.st q).J := Ideal.Quotient.factorₐ O (S.Jinf_le q)

theorem facR_compat (q : ℕ) : (resQ O S.dm (S.st q).J).comp (S.facR q).toRingHom = S.resR :=
  RingHom.ext fun x => Quotient.inductionOn' x fun _ => rfl

theorem cofinal (N : ℕ) : ∃ q, (S.st q).J.I ≤ S.Jinf ⊔ maximalIdeal (PS O S.dm) ^ N := by
  let K : ℕ → Ideal S.Rh := fun q => ((S.st q).J.I).map (Ideal.Quotient.mk S.Jinf)
  have hK : Antitone K := fun q q' h => Ideal.map_mono (stage_le S.s₀ h)
  have hinf : ⨅ q, K q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Jinf, Ideal.mem_iInf]
    intro q
    have hq := (Ideal.mem_iInf.1 hx) q
    obtain ⟨y, hy, hya⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hq
    rw [Ideal.Quotient.eq] at hya
    have : a = y - (y - a) := by ring
    rw [this]
    exact ((S.st q).J.I).sub_mem hy (S.Jinf_le q hya)
  obtain ⟨w, hw⟩ := IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot K hK hinf N
  refine ⟨w, ?_⟩
  have h1 : (S.st w).J.I ≤ (K w).comap (Ideal.Quotient.mk S.Jinf) := Ideal.le_comap_map
  refine h1.trans ((Ideal.comap_mono hw).trans ?_)
  rw [maximalIdeal_Rh, ← Ideal.map_pow, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

section Xi

variable {A : Type u} [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
  (resA : A →+* ResidueField O) (hsA : Function.Surjective resA) (hcA : resA.comp (algebraMap O A) = residue O)

def nA : ℕ := (@exists_pow_maximalIdeal_eq_bot A _ hlA haA).choose

theorem nA_spec : @maximalIdeal A _ hlA ^ nA hlA haA = ⊥ := (@exists_pow_maximalIdeal_eq_bot A _ hlA haA).choose_spec

def qA : ℕ := (S.cofinal (nA hlA haA)).choose

theorem qA_spec : (S.st (S.qA hlA haA)).J.I ≤ S.Jinf ⊔ maximalIdeal (PS O S.dm) ^ nA hlA haA :=
  (S.cofinal (nA hlA haA)).choose_spec

variable (u : S.Rh →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR)

abbrev util : PS O S.dm →ₐ[O] A := u.comp (Ideal.Quotient.mkₐ O S.Jinf)

include hu in
theorem res_util (a : PS O S.dm) : resA (S.util u a) = resS O S.dm a := by
  change (resA.comp u.toRingHom) (Ideal.Quotient.mk S.Jinf a) = _
  rw [hu]; rfl

include haA hu in
theorem maximalIdeal_le_comap : maximalIdeal (PS O S.dm) ≤ (@maximalIdeal A _ hlA).comap (S.util u) := by
  intro a ha
  haveI := hlA; haveI := haA
  rw [Ideal.mem_comap, ← ker_res_eq_maximalIdeal resA, RingHom.mem_ker, res_util S resA u hu, ← RingHom.mem_ker,
    ker_resS]
  exact ha

include hu in
theorem J_qA_le_ker : (S.st (S.qA hlA haA)).J.I ≤ RingHom.ker (S.util u) := by
  refine (S.qA_spec hlA haA).trans (sup_le ?_ ?_)
  · intro a ha
    rw [RingHom.mem_ker]
    change u (Ideal.Quotient.mk S.Jinf a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  · refine (Ideal.pow_right_mono (S.maximalIdeal_le_comap hlA haA resA u hu) _).trans ?_
    refine (Ideal.le_comap_pow _ _).trans ?_
    rw [nA_spec, ← RingHom.ker_eq_comap_bot]

def ubar : Q O S.dm (S.st (S.qA hlA haA)).J →ₐ[O] A :=
  Ideal.Quotient.liftₐ _ (S.util u) fun a ha => S.J_qA_le_ker hlA haA resA u hu ha

theorem ubar_comp : (S.ubar hlA haA resA u hu).comp (Ideal.Quotient.mkₐ O _) = S.util u :=
  AlgHom.ext fun _ => rfl

include hu in
theorem compat_of_comp (q : ℕ) (v : Q O S.dm (S.st q).J →ₐ[O] A)
    (hv : v.comp (Ideal.Quotient.mkₐ O _) = S.util u) : resA.comp v.toRingHom = resQ O S.dm (S.st q).J := by
  refine RingHom.ext fun x => Quotient.inductionOn' x fun a => ?_
  change resA ((v.comp (Ideal.Quotient.mkₐ O _)) a) = resS O S.dm a
  rw [hv, res_util S resA u hu]

theorem ubar_compat : resA.comp (S.ubar hlA haA resA u hu).toRingHom = resQ O S.dm (S.st (S.qA hlA haA)).J :=
  S.compat_of_comp resA u hu _ _ (S.ubar_comp hlA haA resA u hu)

def Ξ : S.F A resA := S.Fmap (S.ubar hlA haA resA u hu) (S.ubar_compat hlA haA resA u hu) (S.st (S.qA hlA haA)).ξ

theorem Ξ_key (q : ℕ) (v : Q O S.dm (S.st q).J →ₐ[O] A) (hv : v.comp (Ideal.Quotient.mkₐ O _) = S.util u) :
    S.Frel (S.Ξ hlA haA resA u hu) (S.Fmap v (S.compat_of_comp resA u hu q v hv) (S.st q).ξ) := by
  rcases le_total q (S.qA hlA haA) with h | h
  ·
    have e : S.ubar hlA haA resA u hu = v.comp (fac (K := (S.st (S.qA hlA haA)).J) (J := (S.st q).J)
        (stage_le S.s₀ h)) := by
      apply Ideal.Quotient.algHom_ext O
      rw [ubar_comp, AlgHom.comp_assoc, fac_comp_mkₐ, hv]
    unfold Ξ
    rw [S.Fmap_congr _ _ (S.ubar_compat hlA haA resA u hu)
      (comp_compat _ (S.compat_of_comp resA u hu q v hv) _ (fac_compat _)) e]
    exact S.htrans _ _ _ (S.Fmap_comp _ _ (fac_compat _) _ _ _)
      (S.Fmap_rel _ _ _ _ (stage_lift' S.s₀ h))
  ·
    have e : v = (S.ubar hlA haA resA u hu).comp (fac (K := (S.st q).J) (J := (S.st (S.qA hlA haA)).J)
        (stage_le S.s₀ h)) := by
      apply Ideal.Quotient.algHom_ext O
      rw [hv, AlgHom.comp_assoc, fac_comp_mkₐ, ubar_comp]
    apply S.hsymm
    rw [S.Fmap_congr _ _ (S.compat_of_comp resA u hu q v hv)
      (comp_compat _ (S.ubar_compat hlA haA resA u hu) _ (fac_compat _)) e]
    exact S.htrans _ _ _ (S.Fmap_comp _ _ (fac_compat _) _ _ _)
      (S.Fmap_rel _ _ _ _ (stage_lift' S.s₀ h))
end Xi

theorem Ξ_nat {A : Type u} [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O)
    {A' : Type u} [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
    (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
    (hcA' : resA'.comp (algebraMap O A') = residue O)
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
    (u : S.Rh →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR) (hfu : resA'.comp (f.comp u).toRingHom = S.resR) :
    S.Frel (S.Ξ hlA' haA' resA' (f.comp u) hfu) (S.Fmap f hf (S.Ξ hlA haA resA u hu)) := by
  have hv : (f.comp (S.ubar hlA haA resA u hu)).comp (Ideal.Quotient.mkₐ O _) = S.util (f.comp u) := by
    rw [AlgHom.comp_assoc, ubar_comp]; rfl
  refine S.htrans _ _ _ (S.Ξ_key hlA' haA' resA' (f.comp u) hfu _ _ hv) ?_
  exact S.Fmap_comp _ _ _ _ _ _

theorem Ξ_surj (hl : IsLocalRing (Dk O)) (ha : IsArtinianRing (Dk O)) (hs : Function.Surjective (resD O))
    (hc : (resD O).comp (algebraMap O (Dk O)) = residue O) (x : S.F (Dk O) (resD O)) :
    ∃ (θ : S.Rh →ₐ[O] Dk O) (hθ : (resD O).comp θ.toRingHom = S.resR), S.Frel (S.Ξ hl ha (resD O) θ hθ) x := by
  obtain ⟨θ, hθ, hθx⟩ := S.ξ₂_surj x
  let v : Q O S.dm (S.st 0).J →ₐ[O] Dk O := θ.comp (S.e₂ : Q O S.dm S.J₂ →ₐ[O] Td O S.dm)
  have hv : (resD O).comp v.toRingHom = resQ O S.dm (S.st 0).J := comp_compat _ hθ _ S.e₂_compat
  let Θ : S.Rh →ₐ[O] Dk O := v.comp (S.facR 0)
  have hΘ : (resD O).comp Θ.toRingHom = S.resR := comp_compat _ hv _ (S.facR_compat 0)
  refine ⟨Θ, hΘ, ?_⟩
  have hvv : v.comp (Ideal.Quotient.mkₐ O _) = S.util Θ := AlgHom.ext fun _ => rfl
  refine S.htrans _ _ _ (S.Ξ_key hl ha (resD O) Θ hΘ 0 v hvv) ?_

  refine S.htrans _ _ _ (S.Fmap_comp (S.e₂ : Q O S.dm S.J₂ →ₐ[O] Td O S.dm) θ S.e₂_compat hθ hv _) ?_
  refine S.htrans _ _ _ (S.Fmap_rel θ hθ _ _ (S.Fmap_gf_id _ S.e₂_symm_compat _ S.e₂_compat ?_ S.ξ₂)) hθx
  exact AlgHom.ext fun t => S.e₂.apply_symm_apply t

theorem Ξ_inj (hl : IsLocalRing (Dk O)) (ha : IsArtinianRing (Dk O)) (hs : Function.Surjective (resD O))
    (hc : (resD O).comp (algebraMap O (Dk O)) = residue O) (Θ Θ' : S.Rh →ₐ[O] Dk O)
    (hΘ : (resD O).comp Θ.toRingHom = S.resR) (hΘ' : (resD O).comp Θ'.toRingHom = S.resR)
    (hrel : S.Frel (S.Ξ hl ha (resD O) Θ hΘ) (S.Ξ hl ha (resD O) Θ' hΘ')) : Θ = Θ' := by

  have hfac : ∀ (Θ : S.Rh →ₐ[O] Dk O), (resD O).comp Θ.toRingHom = S.resR →
      ∃ v : Q O S.dm (S.st 0).J →ₐ[O] Dk O, v.comp (Ideal.Quotient.mkₐ O _) = S.util Θ := by
    intro Θ hΘ
    let c : Fin S.dm → ResidueField O := fun i => (S.util Θ (MvPowerSeries.X i)).snd
    have hX : ∀ i, S.util Θ (MvPowerSeries.X i) = TrivSqZeroExt.inr (c i) := by
      intro i
      refine TrivSqZeroExt.ext ?_ rfl
      change resD O (S.util Θ (MvPowerSeries.X i)) = 0
      rw [res_util S (resD O) Θ hΘ, resS_X]
    haveI := isHausdorff_of_artinian (Dk O)
    have key : S.util Θ = (θc O S.dm c).comp (φ₂ O S.dm) := by
      refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal (Dk O)) _ _ (fun i => ?_) (fun i => ?_)
      · rw [← ker_resD, RingHom.mem_ker, res_util S (resD O) Θ hΘ, resS_X]
      · rw [hX, AlgHom.comp_apply, φ₂_X, θc_inr_single]
    refine ⟨Ideal.Quotient.liftₐ _ (S.util Θ) fun a ha => ?_, AlgHom.ext fun _ => rfl⟩
    rw [key, AlgHom.comp_apply]
    have ha' : φ₂ O S.dm a = 0 := ha
    rw [ha', map_zero]
  obtain ⟨v, hv⟩ := hfac Θ hΘ
  obtain ⟨v', hv'⟩ := hfac Θ' hΘ'
  have h1 := S.Ξ_key hl ha (resD O) Θ hΘ 0 v hv
  have h2 := S.Ξ_key hl ha (resD O) Θ' hΘ' 0 v' hv'
  have h3 : S.Frel (S.Fmap v (S.compat_of_comp (resD O) Θ hΘ 0 v hv) (S.st 0).ξ)
      (S.Fmap v' (S.compat_of_comp (resD O) Θ' hΘ' 0 v' hv') (S.st 0).ξ) :=
    S.htrans _ _ _ (S.hsymm _ _ h1) (S.htrans _ _ _ hrel h2)

  let es : Td O S.dm →ₐ[O] Q O S.dm S.J₂ := S.e₂.symm
  have hve : (resD O).comp (v.comp es).toRingHom = resT O S.dm :=
    comp_compat _ (S.compat_of_comp (resD O) Θ hΘ 0 v hv) _ S.e₂_symm_compat
  have hve' : (resD O).comp (v'.comp es).toRingHom = resT O S.dm :=
    comp_compat _ (S.compat_of_comp (resD O) Θ' hΘ' 0 v' hv') _ S.e₂_symm_compat
  have h4 : S.Frel (S.Fmap (v.comp es) hve S.ξ₂) (S.Fmap (v'.comp es) hve' S.ξ₂) :=
    S.htrans _ _ _ (S.Fmap_comp es v S.e₂_symm_compat _ hve S.ξ₂)
      (S.htrans _ _ _ h3 (S.hsymm _ _ (S.Fmap_comp es v' S.e₂_symm_compat _ hve' S.ξ₂)))
  have h5 := S.ξ₂_inj _ _ hve hve' h4
  have h6 : v = v' := by
    apply AlgHom.ext; intro y
    have := congrArg (fun w : Td O S.dm →ₐ[O] Dk O => w (S.e₂ y)) h5
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
    have hy : es (S.e₂ y) = y := S.e₂.symm_apply_apply y
    exact (congrArg v hy).symm.trans (this.trans (congrArg v' hy))
  apply Ideal.Quotient.algHom_ext O
  change S.util Θ = S.util Θ'
  rw [← hv, ← hv', h6]

def Epb {B A' A : Type u} [CommRing B] [Algebra O B] [CommRing A'] [Algebra O A'] [CommRing A] [Algebra O A]
    (ū : B →ₐ[O] A) (q : A' →ₐ[O] A) : Subalgebra O (B × A') :=
  AlgHom.equalizer (ū.comp (AlgHom.fst O B A')) (q.comp (AlgHom.snd O B A'))

set_option maxHeartbeats 4000000 in
theorem Ξ_lift {A' : Type u} [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
    (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
    (hcA' : resA'.comp (algebraMap O A') = residue O)
    {A : Type u} [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O)
    (q : A' →ₐ[O] A) (hq : resA.comp q.toRingHom = resA') (hqs : Function.Surjective q)
    (t : A') (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA') (hmt : ∀ m ∈ RingHom.ker resA', m * t = 0)
    (hker : ∀ a : A', q a = 0 ↔ a ∈ Ideal.span {t})
    (u : S.Rh →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR) (η' : S.F A' resA')
    (hη : S.Frel (S.Fmap q hq η') (S.Ξ hlA haA resA u hu)) : ∃ u' : S.Rh →ₐ[O] A', q.comp u' = u := by
  haveI := hlA; haveI := haA; haveI := hlA'; haveI := haA'

  let J₀ : Adm O S.dm := (S.st (S.qA hlA haA)).J
  let ū : Q O S.dm J₀ →ₐ[O] A := S.ubar hlA haA resA u hu
  have hū : resA.comp ū.toRingHom = resQ O S.dm J₀ := S.ubar_compat hlA haA resA u hu
  have hūmk : ∀ s, ū (Ideal.Quotient.mk J₀.I s) = u (Ideal.Quotient.mk S.Jinf s) := fun _ => rfl

  have hP0 :=
    IsLocalRing.isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue O (Q O S.dm J₀)
      (resQ O S.dm J₀) (resQ_compat J₀) A' resA' hcA' A resA ū hū q hq
  haveI hlE : IsLocalRing ↥(Epb ū q) := hP0.1
  haveI haE : IsArtinianRing ↥(Epb ū q) := hP0.2.1
  let p' : ↥(Epb ū q) →ₐ[O] Q O S.dm J₀ := (AlgHom.fst O _ A').comp (Epb ū q).val
  let p'' : ↥(Epb ū q) →ₐ[O] A' := (AlgHom.snd O _ A').comp (Epb ū q).val
  let resE : ↥(Epb ū q) →+* ResidueField O := (resQ O S.dm J₀).comp p'.toRingHom
  have hsE' : Function.Surjective resE := hP0.2.2
  clear hP0
  have hp' : (resQ O S.dm J₀).comp p'.toRingHom = resE := rfl
  have hcE : resE.comp (algebraMap O ↥(Epb ū q)) = residue O := by rw [← resQ_compat J₀]; rfl
  have hmemE : ∀ x : Q O S.dm J₀ × A', x ∈ Epb ū q ↔ ū x.1 = q x.2 := fun _ => Iff.rfl
  have hEprop : ∀ b : ↥(Epb ū q), ū (b : Q O S.dm J₀ × A').1 = q (b : Q O S.dm J₀ × A').2 := fun b => (hmemE _).1 b.2
  have hcomm : ū.comp p' = q.comp p'' := AlgHom.ext fun b => hEprop b
  have hp'' : resA'.comp p''.toRingHom = resE := by
    refine RingHom.ext fun b => ?_
    change resA' (b : Q O S.dm J₀ × A').2 = resQ O S.dm J₀ (b : Q O S.dm J₀ × A').1
    rw [← hq, ← hū]
    change resA (q _) = resA (ū _)
    rw [hEprop]
  have hcart : ∀ (a' : Q O S.dm J₀) (a'' : A'), ū a' = q a'' → ∃! b : ↥(Epb ū q), p' b = a' ∧ p'' b = a'' := by
    intro a' a'' h
    refine ⟨⟨(a', a''), h⟩, ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨⟨b₁, b₂⟩, hb⟩ ⟨rfl, rfl⟩
    rfl

  obtain ⟨ζ, hζ₁, hζ₂⟩ := S.hglue ↥(Epb ū q) resE hsE' hcE (Q O S.dm J₀) (resQ O S.dm J₀) (resQ_surjective _)
    (resQ_compat _) A' resA' hsA' hcA' A resA hsA hcA p' hp' p'' hp'' ū hū q hq hcomm hcart hqs
    (S.st (S.qA hlA haA)).ξ η' (S.hsymm _ _ hη)

  have hp'_surj : Function.Surjective p' := fun z => by
    obtain ⟨a', ha'⟩ := hqs (ū z)
    exact ⟨⟨(z, a'), ha'.symm⟩, rfl⟩
  choose ev hev using fun i : Fin S.dm => hp'_surj (Ideal.Quotient.mk J₀.I (MvPowerSeries.X i))
  have hev_mem : ∀ i, ev i ∈ maximalIdeal ↥(Epb ū q) := by
    intro i
    have h0 : resE (ev i) = 0 := by
      change resQ O S.dm J₀ (p' (ev i)) = 0
      rw [hev, resQ_mk, resS_X]
    exact (ker_res_eq_maximalIdeal (B := ↥(Epb ū q)) resE).le (RingHom.mem_ker.2 h0)
  haveI hcE' := isAdicComplete_of_artinian ↥(Epb ū q)
  obtain ⟨w, hw⟩ := MvPowerSeries.exists_algHom_apply_X_eq (𝒪 := O) _ ev hev_mem
  have hpw : p'.comp w = Ideal.Quotient.mkₐ O J₀.I := by
    haveI := isHausdorff_of_artinian (Q O S.dm J₀)
    refine MvPowerSeries.algHom_ext_of_apply_X_mem (maximalIdeal (Q O S.dm J₀)) _ _ (fun i => ?_) (fun i => ?_)
    · rw [AlgHom.comp_apply, hw, hev, ← ker_resQ, RingHom.mem_ker, resQ_mk, resS_X]
    · rw [AlgHom.comp_apply, hw, hev]; rfl
  have hpw' : ∀ s, p' (w s) = Ideal.Quotient.mk J₀.I s := fun s => AlgHom.congr_fun hpw s
  have hw1 : ∀ s, ((w s : ↥(Epb ū q)) : Q O S.dm J₀ × A').1 = Ideal.Quotient.mk J₀.I s := hpw'

  have hres2 : ∀ s, resA' ((w s : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 = resS O S.dm s := by
    intro s
    change (resA'.comp p''.toRingHom) (w s) = _
    rw [hp'']
    change resQ O S.dm J₀ (p' (w s)) = _
    rw [hpw', resQ_mk]

  have hmt' : ∀ m ∈ RingHom.ker resA', ∀ y ∈ Ideal.span ({t} : Set A'), m * y = 0 := by
    intro m hm y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    rw [mul_left_comm, hmt m hm, mul_zero]
  have hOt : ∀ (o : O) (c : A'), residue O o = resA' c → algebraMap O A' o * t = c * t := by
    intro o c hoc
    rw [← sub_eq_zero, ← sub_mul]
    apply hmt
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← RingHom.comp_apply, hcA', hoc]

  have hz₀ : ((0 : Q O S.dm J₀), t) ∈ Epb ū q := by
    rw [hmemE]; change ū 0 = q t
    rw [map_zero, (hker t).2 (Ideal.mem_span_singleton_self t)]

  have hkill : ∀ a ∈ S.Jinf, w a = 0 := by
    by_cases hcase : ∃ s, w s = ⟨((0 : Q O S.dm J₀), t), hz₀⟩
    ·
      obtain ⟨s₁, hs₁⟩ := hcase
      have hwsurj : Function.Surjective w := by
        rintro ⟨⟨z, a'⟩, hb⟩
        obtain ⟨s₂, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hq2 : q (a' - ((w s₂ : ↥(Epb ū q)) : Q O S.dm J₀ × A').2) = 0 := by
          rw [map_sub, sub_eq_zero, ← hEprop (w s₂), hw1]
          exact ((hmemE _).1 hb).symm
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hker _).1 hq2)
        obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (resA' c)
        refine ⟨s₂ + algebraMap O _ o * s₁, ?_⟩
        rw [map_add, map_mul, AlgHom.commutes, hs₁]
        apply Subtype.ext
        change ((w s₂ : ↥(Epb ū q)) : Q O S.dm J₀ × A') + algebraMap O (Q O S.dm J₀ × A') o * ((0 : Q O S.dm J₀), t) =
          (Ideal.Quotient.mk J₀.I s₂, a')
        refine Prod.ext ?_ ?_
        · change ((w s₂ : ↥(Epb ū q)) : Q O S.dm J₀ × A').1 + algebraMap O (Q O S.dm J₀) o * 0 = _
          rw [hw1, mul_zero, add_zero]
        · change ((w s₂ : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 + algebraMap O A' o * t = a'
          rw [hOt o c ho, hc, add_sub_cancel]
      let K : Ideal (PS O S.dm) := RingHom.ker w.toRingHom
      have hK : maximalIdeal (PS O S.dm) * J₀.I ≤ K ∧ K ≤ J₀.I := by
        constructor
        · rw [Ideal.mul_le]
          intro r hr j hj
          change w (r * j) = 0
          rw [map_mul]
          apply Subtype.ext
          change ((w r : ↥(Epb ū q)) : Q O S.dm J₀ × A') * ((w j : ↥(Epb ū q)) : Q O S.dm J₀ × A') = 0
          have hj1 : ((w j : ↥(Epb ū q)) : Q O S.dm J₀ × A').1 = 0 := by
            rw [hw1]; exact Ideal.Quotient.eq_zero_iff_mem.2 hj
          have hj2 : ((w j : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 ∈ Ideal.span ({t} : Set A') := by
            rw [← hker, ← hEprop (w j), hj1, map_zero]
          have hr2 : ((w r : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 ∈ RingHom.ker resA' := by
            rw [RingHom.mem_ker, hres2, ← RingHom.mem_ker, ker_resS]; exact hr
          refine Prod.ext ?_ ?_
          · rw [Prod.fst_mul, hj1, mul_zero]; rfl
          · rw [Prod.snd_mul, hmt' _ hr2 _ hj2]; rfl
        · intro a ha
          have : p' (w a) = 0 := by change p' (w.toRingHom a) = 0; rw [RingHom.mem_ker.1 ha, map_zero]
          rw [hpw'] at this
          exact Ideal.Quotient.eq_zero_iff_mem.1 this
      have hadm : Admissible (S.st (S.qA hlA haA)) K := by
        refine ⟨hK, ?_⟩
        let Kq : Adm O S.dm := sub (S.st (S.qA hlA haA)) K hK
        let ε : Q O S.dm Kq ≃ₐ[O] ↥(Epb ū q) := Ideal.quotientKerAlgEquivOfSurjective hwsurj
        have hε : ∀ s, ε (Ideal.Quotient.mk Kq.I s) = w s := fun s =>
          (Ideal.quotientKerAlgEquivOfSurjective_apply hwsurj _).trans (RingHom.kerLift_mk _ _)
        have hεs : ∀ s, ε.symm (w s) = Ideal.Quotient.mk Kq.I s := fun s => by
          rw [← hε, AlgEquiv.symm_apply_apply]
        have hεc : (resQ O S.dm Kq).comp ε.symm.toAlgHom.toRingHom = resE := by
          refine RingHom.ext fun b => ?_
          obtain ⟨s, rfl⟩ := hwsurj b
          change resQ O S.dm Kq (ε.symm (w s)) = resQ O S.dm J₀ (p' (w s))
          rw [hεs, hpw']; rfl
        have hfe : (fac (K := Kq) (J := J₀) hK.2).comp ε.symm.toAlgHom = p' := by
          refine AlgHom.ext fun b => ?_
          obtain ⟨s, rfl⟩ := hwsurj b
          change fac (K := Kq) (J := J₀) hK.2 (ε.symm (w s)) = p' (w s)
          rw [hεs, fac_mk, hpw']
        have c1 : S.Frel (S.Fmap p' hp' ζ)
            (S.Fmap (fac (K := Kq) (J := J₀) hK.2) (fac_compat _) (S.Fmap ε.symm.toAlgHom hεc ζ)) :=
          S.Fmap_comp' ε.symm.toAlgHom (fac (K := Kq) (J := J₀) hK.2) hεc (fac_compat _) p' hp' hfe ζ
        exact ⟨S.Fmap ε.symm.toAlgHom hεc ζ, S.htrans _ _ _ (S.hsymm _ _ c1) hζ₁⟩
      have hle := step_least (S.st (S.qA hlA haA)) K hadm
      intro a ha
      have : a ∈ K := hle (S.Jinf_le (S.qA hlA haA + 1) ha)
      exact this
    ·
      have hinj : ∀ s s', p' (w s) = p' (w s') → w s = w s' := by
        intro s s' hss
        suffices h : w (s - s') = 0 by rwa [map_sub, sub_eq_zero] at h
        have hδ1 : ((w (s - s') : ↥(Epb ū q)) : Q O S.dm J₀ × A').1 = 0 := by
          change p' (w (s - s')) = 0
          rw [map_sub, map_sub, hss, sub_self]
        have hqy : q ((w (s - s') : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 = 0 := by
          rw [← hEprop (w (s - s')), hδ1, map_zero]
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hker _).1 hqy)
        by_cases hy : ((w (s - s') : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 = 0
        · exact Subtype.ext (Prod.ext hδ1 hy)
        · exfalso
          apply hcase
          have hcu : IsUnit c := by
            rw [isUnit_iff_res_ne_zero resA']
            intro hc0
            apply hy
            rw [← hc]
            exact hmt c hc0
          obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (resA' ↑hcu.unit⁻¹)
          refine ⟨algebraMap O _ o * (s - s'), ?_⟩
          rw [map_mul, AlgHom.commutes]
          apply Subtype.ext
          change algebraMap O (Q O S.dm J₀ × A') o * ((w (s - s') : ↥(Epb ū q)) : Q O S.dm J₀ × A') =
            ((0 : Q O S.dm J₀), t)
          refine Prod.ext ?_ ?_
          · change algebraMap O (Q O S.dm J₀) o * ((w (s - s') : ↥(Epb ū q)) : Q O S.dm J₀ × A').1 = 0
            rw [hδ1, mul_zero]
          · change algebraMap O A' o * ((w (s - s') : ↥(Epb ū q)) : Q O S.dm J₀ × A').2 = t
            rw [← hc, mul_left_comm, hOt o _ ho, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
      intro a ha
      have h0 := hinj a 0 (by
        rw [hpw', hpw', map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (S.Jinf_le (S.qA hlA haA) ha))
      rwa [map_zero] at h0

  let wbar : S.Rh →ₐ[O] ↥(Epb ū q) := Ideal.Quotient.liftₐ S.Jinf w hkill
  refine ⟨p''.comp wbar, ?_⟩
  apply Ideal.Quotient.algHom_ext O
  refine AlgHom.ext fun s => ?_
  change q (p'' (w s)) = u (Ideal.Quotient.mk S.Jinf s)
  rw [← hūmk, ← hpw', ← AlgHom.comp_apply, ← hcomm]
  rfl
end Datum
p2m_reactivate "P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerHull.Datum"

end P2mSchlessingerHull
p2m_reactivate "P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerHull.Datum P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective.P2mSchlessingerHull"

open IsLocalRing in
theorem solution
    (O : Type u) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O]
    (F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u)
    (Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
      F A resA → F A resA → Prop)
    (hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x : F A resA), Frel x x)
    (hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y : F A resA), Frel x y → Frel y x)
    (htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y z : F A resA), Frel x y → Frel y z → Frel x z)
    (Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA')
    (Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
      Frel x y → Frel (Fmap f hf x) (Fmap f hf y))
    (Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x)
    (Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
      (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
      (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
      (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x)))
    (x₀ : F (ResidueField O) (RingHom.id (ResidueField O)))
    (hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀)
    (hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O), Function.Surjective resA' →
        resA'.comp (algebraMap O A') = residue O →
      ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
        (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
        resA''.comp (algebraMap O A'') = residue O →
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
        (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
        (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
        (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
        q'.comp p' = q''.comp p'' →
        (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
        Function.Surjective q'' →
        ∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
          ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'')
    (r : ℕ)
    (e : F (DualNumber (ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom → (Fin r → ResidueField O))
    (he_rel : ∀ x y, Frel x y → e x = e y)
    (he_inj : ∀ x y, e x = e y → Frel x y)
    (he_smul : ∀ (c : ResidueField O)
        (μ : DualNumber (ResidueField O) →ₐ[O] DualNumber (ResidueField O))
        (hμ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp μ.toRingHom =
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ x, e (Fmap μ hμ x) = c • e x)
    (he_add : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
        ∀ (p₁ p₂ σ : B →ₐ[O] DualNumber (ResidueField O))
          (hp₁ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₁.toRingHom = resB)
          (hp₂ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            p₂.toRingHom = resB)
          (hσ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
            σ.toRingHom = resB),
        (∀ b₁ b₂ : B, p₁ b₁ = p₁ b₂ → p₂ b₁ = p₂ b₂ → b₁ = b₂) →
        (∀ t₁ t₂ : DualNumber (ResidueField O), TrivSqZeroExt.fst t₁ = TrivSqZeroExt.fst t₂ →
            ∃ b : B, p₁ b = t₁ ∧ p₂ b = t₂) →
        (∀ b : B, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ y : F B resB, e (Fmap σ hσ y) = e (Fmap p₁ hp₁ y) + e (Fmap p₂ hp₂ y)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R) (_ : Algebra O R)
      (_ : IsAdicComplete (maximalIdeal R) R)
      (resR : R →+* ResidueField O) (_ : resR.comp (algebraMap O R) = residue O)
      (Ξ : ∀ (A : Type u) [CommRing A] [Algebra O A], IsLocalRing A → IsArtinianRing A →
      ∀ (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (u : R →ₐ[O] A), resA.comp u.toRingHom = resR → F A resA),
      (∀ (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
        (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR)
        (hfu : resA'.comp (f.comp u).toRingHom = resR),
        Frel (Ξ A' hlA' haA' resA' hsA' hcA' (f.comp u) hfu) (Fmap f hf (Ξ A hlA haA resA hsA hcA u hu))) ∧
      (∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (θ θ' : R →ₐ[O] DualNumber (ResidueField O))
        (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom = resR)
        (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
          resR),
        Frel (Ξ _ hl ha _ hs hc θ hθ) (Ξ _ hl ha _ hs hc θ' hθ') → θ = θ') ∧
      (∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (x : F (DualNumber (ResidueField O))
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        ∃ (θ : R →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            resR), Frel (Ξ _ hl ha _ hs hc θ hθ) x) ∧
      (∀ (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (q : A' →ₐ[O] A) (hq : resA.comp q.toRingHom = resA'), Function.Surjective q →
        ∀ (t : A'), t ≠ 0 → t ∈ RingHom.ker resA' → (∀ m ∈ RingHom.ker resA', m * t = 0) →
        (∀ a : A', q a = 0 ↔ a ∈ Ideal.span {t}) →
        ∀ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR) (η' : F A' resA'),
        Frel (Fmap q hq η') (Ξ A hlA haA resA hsA hcA u hu) → ∃ u' : R →ₐ[O] A', q.comp u' = u) := by
  let S : P2mSchlessingerHull.Datum O :=
    { F := F, Frel := Frel, hrefl := hrefl, hsymm := hsymm, htrans := htrans, Fmap := Fmap,
      Fmap_rel := Fmap_rel, Fmap_id := Fmap_id, Fmap_comp := Fmap_comp, x₀ := x₀, hx₀ := hx₀,
      hglue := hglue, r := r, e := e, he_rel := he_rel, he_inj := he_inj, he_smul := he_smul,
      he_add := he_add }
  refine ⟨S.Rh, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S.resR,
    S.resR_compat, fun A _ _ hlA haA resA hsA hcA u hu => S.Ξ hlA haA resA u hu, ?_, ?_, ?_, ?_⟩
  · intro A _ _ hlA haA resA hsA hcA A' _ _ hlA' haA' resA' hsA' hcA' f hf u hu hfu
    exact S.Ξ_nat hlA haA resA hsA hcA hlA' haA' resA' hsA' hcA' f hf u hu hfu
  · intro hl ha hs hc θ θ' hθ hθ' h
    exact S.Ξ_inj hl ha hs hc θ θ' hθ hθ' h
  · intro hl ha hs hc x
    exact S.Ξ_surj hl ha hs hc x
  · intro A' _ _ hlA' haA' resA' hsA' hcA' A _ _ hlA haA resA hsA hcA q hq hqs t ht0 htm hmt hker u hu η' hη
    exact S.Ξ_lift hlA' haA' resA' hsA' hcA' hlA haA resA hsA hcA q hq hqs t ht0 htm hmt hker u hu η' hη

end
end S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective
end P2MW
export P2MW.S_IsLocalRing_exists_hull_of_forall_pullback_surjective_of_tangent_injective (solution)

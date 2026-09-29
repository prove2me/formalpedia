-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mul_mem_eq_sum_smul_of_adjoin_sup_eq_top_of_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3ebea323-ec96-5959-98b5-fac7fe67f49a

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mul_mem_eq_sum_smul_of_adjoin_sup_eq_top_of_fractionRing

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (O : Subring ↥F₀),
      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (𝒩₀ : Subring ↥(fieldBar q M')),
      (∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ ↔ ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ O) →
      ∀ f : ↥(fieldBar q M'), ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
        (b : ↥(fieldBar q M')) ≠ 0 ∧ f * (b : ↥(fieldBar q M')) = ∑ i, c i • ((a i : ↥𝒩₀) : ↥(fieldBar q M')) := by
  intro F₀ hK1 hLD O hO 𝒩₀ h𝒩₀ f
  classical
  letI : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  let φ : AlgebraicClosure ℚ →ₐ[↥k₀] ↥(fieldBar q M') :=
    { toRingHom := algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'), commutes' := fun _ => rfl }
  have hφ : ∀ c, φ c = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c := fun c => rfl
  set E₁ : IntermediateField ↥k₀ ↥(fieldBar q M') :=
    IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) with hE₁

  have hE₁le : E₁ ≤ φ.fieldRange := by
    rw [hE₁, IntermediateField.adjoin_le_iff]
    rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hE₁mem : ∀ e : ↥(fieldBar q M'), e ∈ E₁ → ∃ c : AlgebraicClosure ℚ, algebraMap _ _ c = e := by
    intro e he
    obtain ⟨c, hc⟩ := AlgHom.mem_fieldRange.mp (hE₁le he)
    exact ⟨c, hc⟩
  haveI hE₁alg : Algebra.IsAlgebraic ↥k₀ ↥E₁ := by
    refine ⟨fun x => ?_⟩
    obtain ⟨c, hc⟩ := hE₁mem x x.2
    have hcalg : IsAlgebraic ↥k₀ c :=
      IsAlgebraic.extendScalars (R := ℚ) (algebraMap ℚ ↥k₀).injective ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c)
    have : IsAlgebraic ↥k₀ (x : ↥(fieldBar q M')) := by rw [← hc, ← hφ]; exact hcalg.algHom φ
    exact IntermediateField.isAlgebraic_iff.mpr this

  let P : ↥(fieldBar q M') → Prop := fun g =>
    ∃ b : ↥(fieldBar q M'), b ∈ 𝒩₀ ∧ b ≠ 0 ∧ g * b ∈ Submodule.span (AlgebraicClosure ℚ) (𝒩₀ : Set ↥(fieldBar q M'))

  have hmul : ∀ z : ↥(fieldBar q M'), z ∈ Submodule.span (AlgebraicClosure ℚ) (𝒩₀ : Set ↥(fieldBar q M')) →
      ∀ b : ↥(fieldBar q M'), b ∈ 𝒩₀ → z * b ∈ Submodule.span (AlgebraicClosure ℚ) (𝒩₀ : Set ↥(fieldBar q M')) := by
    intro z hz b hb
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (𝒩₀.mul_mem hx hb)
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx
  have hPadd : ∀ g g' : ↥(fieldBar q M'), P g → P g' → P (g + g') := by
    rintro g g' ⟨b, hb, hb0, hgb⟩ ⟨b', hb', hb0', hgb'⟩
    refine ⟨b * b', 𝒩₀.mul_mem hb hb', mul_ne_zero hb0 hb0', ?_⟩
    have : (g + g') * (b * b') = (g * b) * b' + (g' * b') * b := by ring
    rw [this]
    exact Submodule.add_mem _ (hmul _ hgb _ hb') (hmul _ hgb' _ hb)
  have hPmul : ∀ e : ↥(fieldBar q M'), e ∈ E₁.toSubalgebra → ∀ g : ↥(fieldBar q M'), g ∈ F₀.toSubalgebra → P (e * g) := by
    intro e he g hg
    obtain ⟨c, rfl⟩ := hE₁mem e he
    obtain ⟨g₁, h₁, hg₁O, hh₁O, hh₁0, hgh⟩ := hO ⟨g, hg⟩
    refine ⟨(h₁ : ↥(fieldBar q M')), (h𝒩₀ _).mpr ⟨h₁.2, by simpa using hh₁O⟩,
      fun h0 => hh₁0 (Subtype.ext (by simpa using h0)), ?_⟩
    have hval : g * (h₁ : ↥(fieldBar q M')) = (g₁ : ↥(fieldBar q M')) := by
      have := congrArg Subtype.val hgh; simpa using this
    rw [mul_assoc, hval, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span ((h𝒩₀ _).mpr ⟨g₁.2, by simpa using hg₁O⟩))

  have hfmem : f ∈ (E₁.toSubalgebra ⊔ F₀.toSubalgebra) := by
    rw [← IntermediateField.sup_toSubalgebra_of_isAlgebraic E₁ F₀ (Or.inl hE₁alg), hE₁, hK1]
    trivial
  have hfP : P f := by
    rw [← Subalgebra.mem_toSubmodule, ← Subalgebra.mul_toSubmodule] at hfmem
    refine Submodule.mul_induction_on hfmem (fun e he g hg => hPmul e he g hg) (fun x y hx hy => hPadd x y hx hy)
  obtain ⟨b, hb, hb0, hfb⟩ := hfP
  obtain ⟨n, c, a, hsum⟩ := Submodule.mem_span_set'.mp hfb
  refine ⟨n, c, fun i => ⟨(a i : ↥(fieldBar q M')), (a i).2⟩, ⟨b, hb⟩, hb0, ?_⟩
  rw [← hsum]

end S_ModularCurve_FullLevel_exists_mul_mem_eq_sum_smul_of_adjoin_sup_eq_top_of_fractionRing
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mul_mem_eq_sum_smul_of_adjoin_sup_eq_top_of_fractionRing (solution)

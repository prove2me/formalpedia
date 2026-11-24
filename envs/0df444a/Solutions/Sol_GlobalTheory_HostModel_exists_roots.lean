-- Prove2me | solution 1 for GlobalTheory.HostModel.exists_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:12.707073+00:00
-- url     : https://prove2.me/submissions/89610974-fb32-4532-ba92-b6cd4bb0d303

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelOfSplitAndLevelCoeffExist
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HostModel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
namespace GlobalTheory.HostModel
namespace _root_.GlobalTheory.HostModel
theorem _root_.solution (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] (F : Type) [Field F] [IsAlgClosed F]
    (f : L →+* F) :
    ∃ ζ : ℕ → Fˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧
      ∀ n, 0 < n → ∀ z : L, (z : ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n → (ζ n : F) = f z := by
  set S : Set ℂ := (L : Set ℂ) ∪ Set.range (fun n : ℕ => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n + 1)) with hS
  set Kinf := IntermediateField.adjoin ℚ S with hKinf
  have hL : L ≤ Kinf := fun x hx => IntermediateField.subset_adjoin ℚ S (Or.inl hx)
  have hint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x (hx | ⟨n, rfl⟩)
    · exact (IsIntegral.of_finite ℚ (⟨x, hx⟩ : L)).map L.val
    · exact _root_.GlobalTheory.LevelExist.isIntegral_zeta (Nat.succ_pos n)
  haveI : Algebra.IsAlgebraic ℚ Kinf := IntermediateField.isAlgebraic_adjoin hint
  letI : Algebra L Kinf := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  letI : Algebra L F := f.toAlgebra
  haveI : IsScalarTower ℚ L Kinf :=
    IsScalarTower.of_algebraMap_eq fun q => ((IntermediateField.inclusion hL).commutes q).symm
  haveI : Algebra.IsAlgebraic L Kinf := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let g : Kinf →ₐ[L] F := IsAlgClosed.lift
  have hg : ∀ z : L, g (IntermediateField.inclusion hL z) = f z := fun z => g.commutes z
  have hmem : ∀ n, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n ∈ Kinf := by
    intro n
    cases n with
    | zero =>
      have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta 0 = 1 := by
        unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
        simp
      rw [h0]
      exact one_mem _
    | succ n => exact IntermediateField.subset_adjoin ℚ S (Or.inr ⟨n, rfl⟩)
  have hne : ∀ n, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n ≠ 0 := fun n => by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
    exact Complex.exp_ne_zero _
  let w : ℕ → Kinf := fun n => ⟨_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n, hmem n⟩
  have hw0 : ∀ n, g (w n) ≠ 0 := fun n =>
    (map_ne_zero g).mpr fun h => hne n (congrArg Subtype.val h)
  refine ⟨fun n => Units.mk0 (g (w n)) (hw0 n), ?_, ?_, ?_⟩
  · intro n hn
    rw [← IsPrimitiveRoot.coe_units_iff, Units.val_mk0]
    have h1 : IsPrimitiveRoot (w n) n :=
      IsPrimitiveRoot.of_map_of_injective (f := Kinf.val)
        (show IsPrimitiveRoot (Kinf.val (w n)) n from _root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hn)
        Subtype.val_injective
    exact h1.map_of_injective (f := g) (RingHom.injective (g : Kinf →+* F))
  · intro n m hn hm
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow]
    congr 1
    apply Subtype.ext
    show _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta (n * m) ^ m = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta n
    exact _root_.GlobalTheory.HostModel.zeta_mul_pow hn hm
  · intro n hn z hz
    rw [Units.val_mk0, ← hg z]
    congr 1
    exact Subtype.ext hz.symm
end _root_.GlobalTheory.HostModel
end GlobalTheory.HostModel

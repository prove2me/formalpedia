-- Prove2me | solution 1 for GlobalTheory.ZM.exists_prime_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:15.857028+00:00
-- url     : https://prove2.me/submissions/e1172bd7-6ba6-476d-9235-8ed0dc79a482

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelWithOddPrimeFirstNumber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧
      ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  intro E _ _ _ H l
  have hM1 : l.M ≠ 1 := by have := l.three_le; omega
  obtain ⟨n, hn, hnM⟩ := Nat.exists_prime_and_dvd hM1
  have hodd : Odd n := Odd.of_dvd_nat l.odd hnM
  have h3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨n, hn, hodd, fun A₀ hA₀ => ?_⟩
  have hmap : (l.Mb ⊔ Ideal.span {(n : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ⊔ Ideal.span {(n : 𝓞 E)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  have hMn : Ideal.span {(l.M : 𝓞 E)} ≤ Ideal.span {(n : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hnM)
  refine ⟨⟨n, h3, hodd, l.Mb ⊔ Ideal.span {(n : 𝓞 E)}, ?_, ?_, ?_, A₀, hA₀⟩,
    ⟨l.M, l.three_le, l.odd, l.Mb, l.fromK, l.prod, l.coprime, Nat.lcm l.A A₀, Nat.lcm_pos l.A_pos hA₀⟩,
    rfl, rfl, ⟨hnM, le_sup_left, Nat.dvd_lcm_right _ _⟩, ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩⟩
  · apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        intro a ha
        exact ⟨Ideal.mem_sup_left ha.1, ha.2⟩
      · refine Ideal.span_mono ?_
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ _⟩
    · exact Ideal.span_le.2 fun a ha => ha.1
  · rw [hmap, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
    set N : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}
    apply le_antisymm
    · refine sup_le (sup_le hMn ?_) (sup_le ?_ ?_) <;>
        first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    · calc N = N * (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by rw [l.coprime, Ideal.mul_top]
        _ = l.Mb * N ⊔ N * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.mul_sup, mul_comm N l.Mb]
        _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_right)
  · rw [hmap, eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left le_sup_left
end GlobalTheory.ZM

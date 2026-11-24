-- Prove2me | solution 1 for GlobalTheory.UnifParts.exists_inGenus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:20.868037+00:00
-- url     : https://prove2.me/submissions/23462b1e-e9f1-49d8-b405-493b91917a1c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts

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
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.UnifParts
theorem _root_.solution (D : Datum H) (l : Level H) (σ : KA l →+* ℂ)
    (hs : ∀ (l : Level H) (N : ℕ) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) → (l.A : ℤ) ∣ ν - 1 →
      ∃ g : Sim D, (N : ℤ) ∣ g.ν N - ν) : ∃ t, InGenus D l σ D t := by
  have hprim : IsPrimitiveRoot (σ (baseKA l).ζ) l.A := (baseKA l).ζ_prim.map_of_injective σ.injective
  obtain ⟨i, -, hi, hζ⟩ := (Complex.isPrimitiveRoot_iff _ _ l.A_pos.ne').mp hprim
  obtain ⟨s, c, hc⟩ := hs { l with A := 1, A_pos := one_pos } l.A (-(i : ℤ)) l.A_pos
    (Nat.isCoprime_iff_coprime.mpr hi).neg_left (by simp)
  refine ⟨s.f l.M', rfl, rfl, s.f, s.ν, fun n m hn hm a => ?_, fun n hn => ?_, s.mult, ?_, rfl⟩
  · obtain ⟨b, hb⟩ := s.tower n m hn hm a
    exact ⟨b, by rw [← hb]; abel⟩
  · obtain ⟨g, hg⟩ := s.inv n hn
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      obtain ⟨b, hb⟩ := (hg a).1
      exact ⟨g e - b, by rw [smul_sub, ← hb, he, map_nsmul]; abel⟩
    · rintro ⟨e, rfl⟩
      exact ⟨s.f n e, map_nsmul _ _ _⟩
    · obtain ⟨b, hb⟩ := (hg a').2
      exact ⟨g a', -b, by rw [smul_neg, ← hb]; abel⟩
  · have hA : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr l.A_pos.ne'
    have h1 : (s.ν l.A : ℂ) = -(i : ℂ) + l.A * c := by
      have : s.ν l.A = -(i : ℤ) + l.A * c := by linarith
      rw [this]; push_cast; ring
    rw [← hζ, h1, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨c, by field_simp; ring⟩
end GlobalTheory.UnifParts

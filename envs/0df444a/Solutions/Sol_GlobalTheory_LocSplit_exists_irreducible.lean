-- Prove2me | solution 1 for GlobalTheory.LocSplit.exists_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:05.22308+00:00
-- url     : https://prove2.me/submissions/6850a00f-c265-4013-bb7b-11e94bf9935f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_GlobalTheory_LocSplit_exists_val_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K) (hd : DenseRange ι)
  (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
include hd hv
namespace GlobalTheory.LocSplit
theorem _root_.solution (g : F) (hg : p.valuation F g = WithZero.exp (-1 : ℤ)) :
    ∃ q : 𝒪[K], Irreducible q ∧ (q : K) = ι g := by
  have hlt : ∀ x y : F, valuation K (ι x) < valuation K (ι y) ↔
      p.valuation F x < p.valuation F y := fun x y => by rw [← not_le, ← not_le, hv]
  have h1 : valuation K (ι g) < 1 := by
    have := (hlt g 1).2 (by rw [hg, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using this
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg; exact WithZero.exp_ne_zero hg.symm
  have hI := Valuation.integer.integers (valuation K)
  refine ⟨⟨ι g, h1.le⟩, ⟨fun hu => h1.ne (hI.one_of_isUnit hu), fun a b hab => ?_⟩, rfl⟩
  have hab' : ι g = (a : K) * b := congrArg Subtype.val hab
  have hne : (a : K) * b ≠ 0 := by rw [← hab']; simpa using hg0
  by_contra hcon
  rw [not_or] at hcon
  have key : ∀ c : 𝒪[K], (c : K) ≠ 0 → ¬ IsUnit c → ∃ y : F, valuation K (ι y) = valuation K c ∧
      p.valuation F y ≤ WithZero.exp (-1 : ℤ) := by
    intro c hc hu
    obtain ⟨y, hy0, hy⟩ := exists_val_eq ι hd c hc
    refine ⟨y, hy, ?_⟩
    have h2 : valuation K (c : K) < 1 :=
      lt_of_le_of_ne c.2 fun h => hu (hI.isUnit_of_one' h)
    have h3 : p.valuation F y < 1 := by
      have := (hlt y 1).1 (by simpa [hy] using h2)
      simpa using this
    have h0 : p.valuation F y ≠ 0 := by simpa using hy0
    rw [← WithZero.exp_log h0] at h3 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
    rw [WithZero.exp_le_exp]
    omega
  obtain ⟨y, hy, hy1⟩ := key a (left_ne_zero_of_mul hne) hcon.1
  obtain ⟨z, hz, hz1⟩ := key b (right_ne_zero_of_mul hne) hcon.2
  have h4 := (hv g (y * z)).1 (by rw [hab', map_mul, map_mul, map_mul, hy, hz])
  rw [map_mul, hg] at h4
  have h5 := h4.trans (mul_le_mul' hy1 hz1)
  rw [← WithZero.exp_add, WithZero.exp_le_exp] at h5
  omega
end GlobalTheory.LocSplit

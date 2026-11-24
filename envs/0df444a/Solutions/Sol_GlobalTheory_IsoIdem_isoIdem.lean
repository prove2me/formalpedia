-- Prove2me | solution 1 for GlobalTheory.IsoIdem.isoIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:11:03.851541+00:00
-- url     : https://prove2.me/submissions/7747ccfe-bb07-47bc-a37a-7c8253951018

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommuteOfCommuteSeparableCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsotropicIdempotentCentralizerHermitian
import Theorems.Thm_GlobalTheory_IsoIdem_eq_zero_of_pow_eq_zero
import Theorems.Thm_GlobalTheory_IsoIdem_exists_pow_mul_eq
import Theorems.Thm_GlobalTheory_IsoIdem_star_mul_comm
import Theorems.Thm_GlobalTheory_IsoIdem_pow_add_mul_pow
import Theorems.Thm_GlobalTheory_CommSep_commute_of_commute_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IsoIdem
namespace GlobalTheory.IsoIdem
theorem _root_.solution : ∀ (E : Type) [Field E] [StarRing E] (r : ℕ) (A₀ : Matrix (Fin r) (Fin r) E),
    A₀.IsHermitian → A₀.charpoly.Separable → ∃ f : Matrix (Fin r) (Fin r) E, f * A₀ = A₀ * f ∧
      f * f = f ∧ f * star f = 0 ∧ ∀ y : Matrix (Fin r) (Fin r) E, y * A₀ = A₀ * y →
        y * (1 - f - star f) * star (y * (1 - f - star f)) = 0 → y * (1 - f - star f) = 0 := by
  intro E _ _ r A hA hs
  have comm : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b → a * b = b * a :=
    GlobalTheory.CommSep.commute_of_commute_separable E r A hs
  have cstar := star_mul_comm A hA
  have cmul : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a * b) * A = A * (a * b) := by
    intro a b ha hb; rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  have cadd : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a + b) * A = A * (a + b) := by
    intro a b ha hb; rw [add_mul, mul_add, ha, hb]
  have csub : ∀ a b : Matrix (Fin r) (Fin r) E, a * A = A * a → b * A = A * b →
      (a - b) * A = A * (a - b) := by
    intro a b ha hb; rw [sub_mul, mul_sub, ha, hb]
  have cone : (1 : Matrix (Fin r) (Fin r) E) * A = A * 1 := by simp
  have cpow : ∀ a : Matrix (Fin r) (Fin r) E, a * A = A * a → ∀ k : ℕ, a ^ k * A = A * a ^ k := by
    intro a ha k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact cmul _ _ ih ha
  let S : Set (Matrix (Fin r) (Fin r) E) := {f | f * A = A * f ∧ f * f = f ∧ f * star f = 0}
  obtain ⟨f, ⟨hfC, hff, hfs⟩, hmax⟩ :=
    (measure fun f : Matrix (Fin r) (Fin r) E => r - f.rank).wf.has_min S ⟨0, by simp [S]⟩
  refine ⟨f, hfC, hff, hfs, ?_⟩
  intro y hy hiso
  by_contra hz
  set e := 1 - f - star f with he
  set z := y * e with hzdef
  have hfsC := cstar f hfC
  have heC : e * A = A * e := csub _ _ (csub _ _ cone hfC) hfsC
  have hzC : z * A = A * z := cmul _ _ hy heC
  have hsf : star f * f = 0 := by rw [← comm f (star f) hfC hfsC]; exact hfs
  have hsfsf : star f * star f = star f := by rw [← star_mul, hff]
  have hfe : f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hff, hfs]; abel
  have hsfe : star f * e = 0 := by rw [he, mul_sub, mul_sub, mul_one, hsf, hsfsf]; abel
  have hef : e * star f = 0 := by rw [← comm _ _ hfsC heC]; exact hsfe
  have hee : e * e = e := by
    calc e * e = (1 - f - star f) * e := by rw [← he]
      _ = e := by rw [sub_mul, sub_mul, one_mul, hfe, hsfe, sub_zero, sub_zero]
  have hestar : star e = e := by
    rw [he, star_sub, star_sub, star_one, star_star, sub_right_comm]
  have hze : z * e = z := by rw [hzdef, mul_assoc, hee]
  obtain ⟨n, w, hwC, hw⟩ := exists_pow_mul_eq A hs z hzC
  have hw' : z ^ (n + 1 + 1) * w = z ^ (n + 1) := by
    rw [pow_succ' z (n + 1), mul_assoc, hw, ← pow_succ']
  have key := pow_add_mul_pow z w (n + 1) hw' (n + 1)
  have hzw : Commute z w := comm _ _ hzC hwC
  set g := z ^ (n + 1) * w ^ (n + 1) with hg
  have hgC : g * A = A * g := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgz : g * z ^ (n + 1) = z ^ (n + 1) := by
    rw [hg, mul_assoc, ((hzw.pow_pow (n + 1) (n + 1)).symm).eq, ← mul_assoc, ← pow_add, key]
  have hgg : g * g = g := by
    conv_lhs => rw [hg]
    rw [← mul_assoc, hgz]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hgz
    exact hz (eq_zero_of_pow_eq_zero A hs z hzC _ hgz.symm)
  set a := z ^ n * w ^ (n + 1) with ha
  have haC : a * A = A * a := cmul _ _ (cpow _ hzC _) (cpow _ hwC _)
  have hgza : g = z * a := by rw [hg, ha, pow_succ', mul_assoc]
  have hgs : g * star g = 0 := by
    have hb : (a * star a) * A = A * (a * star a) := cmul _ _ haC (cstar _ haC)
    rw [hgza, star_mul, mul_assoc, ← mul_assoc a, comm _ _ hb (cstar _ hzC), ← mul_assoc]
    rw [show z * star z = 0 from hiso, zero_mul]
  have hge : g * e = g := by
    rw [hgza, mul_assoc, comm a e haC heC, ← mul_assoc, hze]
  have hfz : f * z = 0 := by
    rw [hzdef, ← mul_assoc, comm f y hfC hy, mul_assoc, hfe, mul_zero]
  have hfg : f * g = 0 := by rw [hgza, ← mul_assoc, hfz, zero_mul]
  have hgf : g * f = 0 := by rw [comm g f hgC hfC]; exact hfg
  have hfsg : f * star g = 0 := by
    rw [← hge, star_mul, hestar, ← mul_assoc, hfe, zero_mul]
  have hgsf : g * star f = 0 := by rw [← hge, mul_assoc, hef, mul_zero]
  have hf'S : f + g ∈ S := by
    refine ⟨cadd _ _ hfC hgC, ?_, ?_⟩
    · rw [add_mul, mul_add, mul_add, hff, hfg, hgf, hgg]; abel
    · rw [star_add, add_mul, mul_add, mul_add, hfs, hfsg, hgsf, hgs]; abel
  have hrank : f.rank < (f + g).rank := by
    unfold Matrix.rank
    apply Submodule.finrank_lt_finrank_of_lt
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · have h1 : (f + g) * f = f := by rw [add_mul, hff, hgf, add_zero]
      calc LinearMap.range f.mulVecLin = LinearMap.range ((f + g) * f).mulVecLin := by rw [h1]
        _ ≤ _ := by rw [Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · obtain ⟨v, hv⟩ : ∃ v : Fin r → E, g *ᵥ v ≠ 0 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        apply hg0
        ext i j
        have := congrFun (hall (Pi.single j 1)) i
        simpa [Matrix.mulVec_single] using this
      refine ⟨g *ᵥ v, ⟨g *ᵥ v, ?_⟩, ?_⟩
      · rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hfg, hgg, zero_add]
      · rintro ⟨u, hu⟩
        rw [Matrix.mulVecLin_apply] at hu
        apply hv
        have hgv : g *ᵥ v = g *ᵥ (g *ᵥ v) := by rw [Matrix.mulVec_mulVec, hgg]
        rw [hgv, ← hu, Matrix.mulVec_mulVec, hgf, Matrix.zero_mulVec]
  have hle : (f + g).rank ≤ r := by
    simpa using Matrix.rank_le_card_width (f + g)
  exact hmax (f + g) hf'S (show r - (f + g).rank < r - f.rank by omega)
end GlobalTheory.IsoIdem

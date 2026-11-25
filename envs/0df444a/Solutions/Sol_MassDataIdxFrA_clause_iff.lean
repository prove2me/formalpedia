-- Prove2me | solution 1 for MassDataIdxFrA.clause_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:29.832267+00:00
-- url     : https://prove2.me/submissions/80859279-1ebd-484f-88b6-641b37ae7b42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxFrA
open Matrix
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace MassDataIdxFrA
theorem _root_.solution (hker : RingHom.ker π = Ideal.span {γ}) (Y : Matrix ι ι O) {β : Type} (u : β → ι → F)
    (pos : β → ι) (hu : ∀ b, ∃ z, IntVec O z ∧ u b = Pi.single (pos b) 1 + (γ : F) • z) (s : Set β)
    (w : ι → F) (j : ι) (hw : ∃ z, IntVec O z ∧ w = Pi.single j 1 + (γ : F) • z) :
    CongSpan O γ (u '' s) ((Y.map ((↑) : O → F) - 1) *ᵥ w) ↔
      ∀ i, i ∉ pos '' s → π (Y i j) = if i = j then 1 else 0 := by
  classical
  have hdiv : ∀ a : O, π a = 0 ↔ ∃ c : O, a = γ * c := by
    intro a
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [← hc, mul_comm]⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, mul_comm]⟩
  have hsm : ∀ (a : O) (x : ι → F), a • x = (a : F) • x := fun a x => rfl
  obtain ⟨z, hz, rfl⟩ := hw
  set Y' := Y.map ((↑) : O → F) with hY'
  let cO : ι → O := fun i => Y i j - (if i = j then 1 else 0)
  have hcO : ∀ i, (cO i : F) = (Y i j : F) - (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j <;> simp [cO, hij]
  have hcol : (Y' - 1) *ᵥ Pi.single j (1 : F) = ∑ i, (cO i : F) • Pi.single i (1 : F) := by
    ext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, hcO]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hY', Matrix.one_apply]
  have hint : ∀ i, ((Y' - 1) *ᵥ z) i ∈ O := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, hY', Matrix.map_apply]
    refine _root_.sum_mem fun l _ => mul_mem (sub_mem (Y i l).2 ?_) (hz l)
    split_ifs
    · exact one_mem O
    · exact zero_mem O
  have hentry : ∀ i, ((Y' - 1) *ᵥ (Pi.single j 1 + (γ : F) • z)) i =
      (cO i : F) + (γ : F) * ((Y' - 1) *ᵥ z) i := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hcol,
      Finset.sum_apply]
    simp [Pi.single_apply]
  constructor
  · rintro ⟨W, hW, z', hz', hv⟩ i hi
    have key : ∀ v ∈ Submodule.span O (u '' s), ∃ c : O, v i = (γ : F) * c := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, rfl⟩ := hx
        obtain ⟨zb, hzb, hub⟩ := hu b
        refine ⟨⟨zb i, hzb i⟩, ?_⟩
        have hne : i ≠ pos b := fun h => hi ⟨b, hb, h.symm⟩
        simp [hub, Pi.single_apply, hne]
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c1, h1⟩ := hx
        obtain ⟨c2, h2⟩ := hy
        exact ⟨c1 + c2, by rw [Pi.add_apply, h1, h2]; push_cast; ring⟩
      | smul a x _ hx =>
        obtain ⟨c, h⟩ := hx
        refine ⟨a * c, ?_⟩
        rw [hsm, Pi.smul_apply, smul_eq_mul, h]
        push_cast
        ring
    obtain ⟨c, hc⟩ := key W hW
    have hvi := congrFun hv i
    rw [hentry i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc] at hvi
    have hO : cO i = γ * ⟨(c : F) + z' i - ((Y' - 1) *ᵥ z) i,
        sub_mem (add_mem c.2 (hz' i)) (hint i)⟩ := by
      apply Subtype.ext
      show (cO i : F) = (γ : F) * ((c : F) + z' i - ((Y' - 1) *ᵥ z) i)
      linear_combination hvi
    have h0 := (hdiv _).2 ⟨_, hO⟩
    simp only [cO, map_sub, sub_eq_zero] at h0
    rw [h0]
    split_ifs <;> simp
  · intro hcond
    have hsel : ∀ i, i ∈ pos '' s → ∃ b, b ∈ s ∧ pos b = i := fun i hi => hi
    choose bsel hbs hpos using hsel
    have hout : ∀ i, i ∉ pos '' s → ∃ e : O, cO i = γ * e := by
      intro i hi
      apply (hdiv _).1
      simp only [cO, map_sub, hcond i hi]
      split_ifs <;> simp
    choose dsel hdsel using hout
    choose zb hzb hub using hu
    refine ⟨∑ i, (if h : i ∈ pos '' s then cO i • u (bsel i h) else 0), ?_,
      ∑ i, ((if h : i ∈ pos '' s then 0 else (dsel i h : F) • Pi.single i (1 : F)) -
        (if h : i ∈ pos '' s then (cO i : F) • zb (bsel i h) else 0)) + (Y' - 1) *ᵥ z, ?_, ?_⟩
    · refine _root_.sum_mem fun i _ => ?_
      split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨bsel i h, hbs i h, rfl⟩)
      · exact Submodule.zero_mem _
    · intro l
      rw [Pi.add_apply, Finset.sum_apply]
      refine add_mem (_root_.sum_mem fun i _ => ?_) (hint l)
      rw [Pi.sub_apply]
      refine sub_mem ?_ ?_
      · split_ifs with h
        · exact zero_mem O
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (dsel i h).2 (by rw [Pi.single_apply]; split_ifs; exacts [one_mem O, zero_mem O])
      · split_ifs with h
        · rw [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (cO i).2 (hzb _ l)
        · exact zero_mem O
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hcol, smul_add, Finset.smul_sum, ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : i ∈ pos '' s
      · simp only [h, dif_pos, hsm, hub, hpos i h, sub_zero, zero_sub, smul_add, smul_neg, smul_smul]
        rw [mul_comm]
        abel
      · simp only [h, dif_neg, not_false_eq_true, sub_zero, zero_add, smul_smul]
        rw [hdsel i h]
        push_cast
        rfl
end MassDataIdxFrA

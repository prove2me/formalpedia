-- Prove2me | solution 1 for GlobalTheory.HL.norm_orbit_sum_le_of_symm_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:19.02445+00:00
-- url     : https://prove2.me/submissions/905e7ffd-de59-4e55-b837-351cfdea4167

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel
import Theorems.Thm_GlobalTheory_HL_sum_eq_sum_of_symm_rel
import Theorems.Thm_GlobalTheory_HL_ncard_stabilizer_orbit
import Theorems.Thm_GlobalTheory_HL_relIndex_stabilizer_smul
import Theorems.Thm_GlobalTheory_HL_invVol_mul_relIndex_comm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {G X : Type} [Group G] [MulAction G X] (St K0 : Subgroup G) (P : X → Prop) (om : X → ℂ) (m : X → X → ℝ) (e : ℝ), K0 ≤ St → (∀ h ∈ St, ∀ x, P x → P (h • x) ∧ om (h • x) = om x ∧ invVol K0 (St ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (St ⊓ MulAction.stabilizer G x) ∧ ∀ y, P y → m (h • x) (h • y) = m x y) → (∀ x, P x → K0.relIndex (St ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (St ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ ‖om x‖ = 1 ∧ {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ e ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * om y‖ ≤ e) → {o : MulAction.orbitRel.Quotient St X | P o.out}.Finite → ‖∑' o : MulAction.orbitRel.Quotient St X, if P o.out then ((invVol K0 (St ⊓ MulAction.stabilizer G o.out) : ℝ) : ℂ) * om o.out else 0‖ ≤ 2 * e * ∑' o : MulAction.orbitRel.Quotient St X, if P o.out then invVol K0 (St ⊓ MulAction.stabilizer G o.out) else 0 := by
  intro G X _ _ St K0 P om m e _ hinv hP hfin
  set mu : X → ℝ := fun x => invVol K0 (St ⊓ MulAction.stabilizer G x) with hmu
  have hN : ∀ x, ∃ s : Finset X, P x → ∀ y, y ∈ s ↔ P y ∧ m x y ≠ 0 := by
    intro x
    by_cases hx : P x
    · exact ⟨(hP x hx).2.2.2.1.toFinset, fun _ y => by simp⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose N hN using hN
  have hO : ∀ o, o ∈ hfin.toFinset ↔ P o.out := fun o => by simp
  generalize hfin.toFinset = O at hO
  have hR : ∀ x, P x → |(∑ y ∈ N x, m x y) - 1| ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.1
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => m x y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => m x y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    exact ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
  have hS : ∀ x, P x → ‖∑ y ∈ N x, (m x y : ℂ) * om y‖ ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.2
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => (m x y : ℂ) * om y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => (m x y : ℂ) * om y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    refine ⟨fun h => ⟨h, fun h0 => hy ?_⟩, fun h => h.1⟩
    simp [h0]
  have hpos : ∀ x, P x → 0 < mu x := fun x hx =>
    (invVol_mul_pos_le_conj K0 _ _ (hP x hx).1 (hP x hx).2.1 (hP x hx).1 (hP x hx).2.1).2.1
  have t1 : (∑' o : MulAction.orbitRel.Quotient St X,
      if P o.out then ((mu o.out : ℝ) : ℂ) * om o.out else 0) =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  have t2 : (∑' o : MulAction.orbitRel.Quotient St X, if P o.out then mu o.out else 0) =
      ∑ o ∈ O, mu o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  refine (congrArg norm t1).trans_le (le_of_le_of_eq ?_ (congrArg (2 * e * ·) t2.symm))
  have huniq : ∀ (o o' : MulAction.orbitRel.Quotient St X) (g : G), g ∈ St →
      g • o.out = o'.out → o = o' := by
    intro o o' g hg h
    rw [← Quotient.out_eq o, ← Quotient.out_eq o']
    exact (Quotient.sound (show MulAction.orbitRel St X o'.out o.out from ⟨⟨g, hg⟩, h⟩)).symm
  have hrep : ∀ z : X, ∃ o : MulAction.orbitRel.Quotient St X, ∃ g ∈ St, g • z = o.out := by
    intro z
    obtain ⟨⟨g, hg⟩, h⟩ : MulAction.orbitRel St X (Quotient.mk _ z).out z := Quotient.mk_out z
    exact ⟨_, g, hg, h⟩
  have unf : ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om z) =
      ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om o.out) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    set Z := O.sigma fun o => N o.out with hZ
    have mZ : ∀ p, p ∈ Z ↔ P p.1.out ∧ P p.2 ∧ m p.1.out p.2 ≠ 0 := by
      intro p
      rw [hZ, Finset.mem_sigma, hO]
      exact and_congr_right fun h => hN _ h _
    let r : (Σ _ : MulAction.orbitRel.Quotient St X, X) →
        (Σ _ : MulAction.orbitRel.Quotient St X, X) → Prop :=
      fun p q => ∃ g ∈ St, g • p.2 = q.1.out ∧ g • p.1.out = q.2
    have hr : ∀ p q, r p q → r q p := by
      rintro p q ⟨g, hg, h1, h2⟩
      exact ⟨g⁻¹, St.inv_mem hg, by rw [← h2, inv_smul_smul], by rw [← h1, inv_smul_smul]⟩
    have hm : ∀ p ∈ Z, ∀ q, r p q → m q.1.out q.2 = m p.1.out p.2 := by
      rintro p hp q ⟨g, hg, h1, h2⟩
      obtain ⟨a, b, -⟩ := (mZ p).1 hp
      rw [← h1, ← h2, (hinv g hg _ b).2.2.2 _ a, ((hP _ b).2.2.2.2.1 _ a).2]
    have hmem : ∀ p ∈ Z, ∀ q, r p q → q ∈ Z := by
      intro p hp q hpq
      have := hm p hp q hpq
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      rw [mZ, this, ← h1, ← h2]
      exact ⟨(hinv g hg _ b).1, (hinv g hg _ a).1, c⟩
    have hdeg : ∀ p ∈ Z, ∀ q, r p q → (Z.filter (r p)).card =
        (St ⊓ MulAction.stabilizer G q.2).relIndex (St ⊓ MulAction.stabilizer G q.1.out) := by
      rintro p hp ⟨o, w⟩ ⟨g, hg, h1, h2⟩
      dsimp only at h1 h2 ⊢
      rw [← ncard_stabilizer_orbit, ← Set.ncard_coe_finset,
        ← Set.ncard_image_of_injective _ (sigma_mk_injective (β := fun _ => X) (i := o))]
      congr 1
      ext ⟨o', w'⟩
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨-, g', hg', h1', h2'⟩
        dsimp only at h1' h2'
        have e1 : (g' * g⁻¹) • o.out = o'.out := by
          rw [← h1, mul_smul, inv_smul_smul, h1']
        have hgg := St.mul_mem hg' (St.inv_mem hg)
        obtain rfl := huniq _ _ _ hgg e1
        refine ⟨w', ⟨_, hgg, e1, ?_⟩, rfl⟩
        rw [← h2, mul_smul, inv_smul_smul, h2']
      · rintro ⟨w'', ⟨h, hh, e1, e2⟩, e3⟩
        rw [← e3]
        have : r p ⟨o, w''⟩ :=
          ⟨h * g, St.mul_mem hh hg, by rw [mul_smul, h1, e1], by rw [mul_smul, h2, e2]⟩
        exact ⟨hmem p hp _ this, this⟩
    refine sum_eq_sum_of_symm_rel Z r hr ?_ _ _ ?_
    · intro p hp
      obtain ⟨o, g, hg, h⟩ := hrep p.2
      have : r p ⟨o, g • p.1.out⟩ := ⟨g, hg, h, rfl⟩
      exact ⟨_, hmem p hp _ this, this⟩
    · intro p hp q hq hpq
      rw [hdeg p hp q hpq, hdeg q hq p (hr _ _ hpq), hm p hp q hpq]
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      have e1 := invVol_mul_relIndex_comm K0 _ _ (hP _ a).1 (hP _ a).2.1 (hP _ b).1 (hP _ b).2.1
      have e2 := congrArg (fun t : ℝ => (t : ℂ)) e1
      rw [← h1, ← h2, relIndex_stabilizer_smul St hg, (hinv g hg _ b).2.1]
      simp only [hmu]
      rw [(hinv g hg _ b).2.2.1]
      push_cast at e2
      linear_combination (m p.1.out p.2 : ℂ) * om p.2 * e2
  have dec : ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z) -
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out * (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ) := by
    simp only [Finset.mul_sum]
    rw [unf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  rw [dec]
  refine (norm_sub_le _ _).trans ?_
  have b1 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z)‖ ≤
      ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _ h), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS _ h) (hpos _ h).le
  have b2 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out *
      (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ)‖ ≤ ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hpos _ h), (hP _ h).2.2.1, mul_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hR _ h) (hpos _ h).le
  rw [← Finset.mul_sum] at b1 b2
  linarith
end GlobalTheory.HL

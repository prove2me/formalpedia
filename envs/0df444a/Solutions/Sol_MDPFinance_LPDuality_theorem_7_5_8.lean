-- Prove2me | solution 1 for MDPFinance.LPDuality.theorem_7_5_8
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:38:50.057266+00:00
-- url     : https://prove2.me/submissions/cba80910-262a-45cb-bd62-989a0b7f95d8

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_LP

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace LPCex

/-- transition: state `true` is absorbing; from `false`, action `0` stays, other actions go to
`true`. -/
def gg : Bool × Fin 3 → Bool := fun p => if p.1 then true else (if p.2 = 0 then false else true)

def rr : Bool × Fin 3 → ℝ := fun p => if p.1 then -1 else (if p.2 = 0 then -2 else -1)

def bb : Bool → ℝ := fun x => if x then 1 else 2

noncomputable def M0 : MarkovDecisionModel Bool (Fin 3) where
  D := (Set.univ : Set Bool) ×ˢ ({0, 1} : Set (Fin 3))
  hD_meas := MeasurableSet.of_discrete
  hD_graph := ⟨fun _ => 0, measurable_const, fun _ => by simp⟩
  Q := Kernel.deterministic gg Measurable.of_discrete
  isMarkovQ := inferInstance
  r := rr
  hr_meas := Measurable.of_discrete
  β := 1 / 2
  hβ0 := by norm_num
  hβ1 := by norm_num

theorem Q_eq (p : Bool × Fin 3) : M0.Q p = Measure.dirac (gg p) := by
  show Kernel.deterministic gg Measurable.of_discrete p = _
  rw [Kernel.deterministic_apply]

theorem Dx_eq (x : Bool) : M0.Dx x = {0, 1} := by
  ext a
  simp [MarkovDecisionModel.Dx, M0]

theorem eI_dirac (y : Bool) (w : Bool → EReal) : erealIntegral (Measure.dirac y) w = w y := by
  unfold erealIntegral
  rw [lintegral_dirac, lintegral_dirac]
  generalize w y = z
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_neg]
    have h1 : (((t : EReal) ⊔ 0).toENNReal : EReal) = ((max t 0 : ℝ) : EReal) := by
      rcases le_total t 0 with h | h
      · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
      · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
        simp [EReal.coe_ennreal_ofReal, h]
    have h2 : ((((-t : ℝ) : EReal) ⊔ 0).toENNReal : EReal) = ((max (-t) 0 : ℝ) : EReal) := by
      rcases le_total (-t) 0 with h | h
      · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
      · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
        simp [EReal.coe_ennreal_ofReal, h]
    rw [h1, h2, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

noncomputable def a (n : ℕ) : ℝ := -2 + 2 * (1 / 2 : ℝ) ^ n

theorem a_succ (n : ℕ) : -1 + 1 / 2 * a n = a (n + 1) := by
  unfold a; rw [pow_succ]; ring

theorem J_true (n : ℕ) : ∀ π : ℕ → Bool → Fin 3, Jnpi M0 M0.r π n true = ((a n : ℝ) : EReal) := by
  induction n with
  | zero => intro π; simp [Jnpi, a]
  | succ n ih =>
    intro π
    show ((rr (true, π 0 true) : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) *
      erealIntegral (M0.Q (true, π 0 true)) (Jnpi M0 M0.r (fun k => π (k + 1)) n) = _
    rw [Q_eq, eI_dirac]
    have : gg (true, π 0 true) = true := rfl
    rw [this, ih, ← EReal.coe_mul, ← EReal.coe_add, ← a_succ]
    simp [rr]

def πs : ℕ → Bool → Fin 3 := fun _ x => if x then 0 else 1

theorem J_false (n : ℕ) : Jnpi M0 M0.r πs n false = ((a n : ℝ) : EReal) := by
  cases n with
  | zero => simp [Jnpi, a]
  | succ n =>
    show ((rr (false, πs 0 false) : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) *
      erealIntegral (M0.Q (false, πs 0 false)) (Jnpi M0 M0.r (fun k => πs (k + 1)) n) = _
    rw [Q_eq, eI_dirac]
    have : gg (false, πs 0 false) = true := rfl
    rw [this]
    have hs : (fun k => πs (k + 1)) = πs := rfl
    rw [hs, J_true, ← EReal.coe_mul, ← EReal.coe_add, ← a_succ]
    simp [rr, πs]

theorem a_ge (n : ℕ) : -2 ≤ a n := by
  unfold a
  have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  linarith

theorem a_le (n : ℕ) (hn : 2 ≤ n) : a n ≤ -3 / 2 := by
  unfold a
  have : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  nlinarith

theorem Jinf_true_le : Jinf M0 true ≤ ((-3 / 2 : ℝ) : EReal) := by
  unfold Jinf
  refine iSup₂_le fun π _ => ?_
  unfold Jinfpi
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  rw [Filter.eventually_atTop]
  exact ⟨2, fun n hn => by rw [J_true]; exact_mod_cast a_le n hn⟩

theorem πs_policy : IsPolicyOf M0 πs := fun k =>
  ⟨Measurable.of_discrete, fun x => by cases x <;> simp [M0, πs]⟩

theorem Jinf_false_ge : ((-2 : ℝ) : EReal) ≤ Jinf M0 false := by
  unfold Jinf
  refine le_trans ?_ (le_iSup₂ (f := fun π (_ : π ∈ {π | IsPolicyOf M0 π}) =>
    Jinfpi M0 M0.r π false) πs πs_policy)
  unfold Jinfpi
  refine Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall fun n => ?_)
    (by isBoundedDefault)
  rw [J_false]
  exact_mod_cast a_ge n

/-- the real integral against a Dirac mass. -/
theorem int_Q (v : Bool → ℝ) (p : Bool × Fin 3) : ∫ x', v x' ∂(M0.Q p) = v (gg p) := by
  rw [Q_eq, integral_dirac]

def IMs : Set (Bool → ℝ) := {v | ∃ c : ℝ, v = fun x => c * bb x}

theorem bb_pos (x : Bool) : 0 < bb x := by cases x <;> simp [bb]

theorem inner_eq (v : Bool → ℝ) (x : Bool) (k : Fin 3) :
    (⨆ (_ : k ∈ M0.Dx x), M0.r (x, k) + M0.β * ∫ x', v x' ∂(M0.Q (x, k))) =
      if k = 2 then 0 else rr (x, k) + 1 / 2 * v (gg (x, k)) := by
  rw [Dx_eq, int_Q]
  fin_cases k
  · simp only [Fin.zero_eta, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, ciSup_unique]
    rfl
  · simp only [Fin.mk_one, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, ciSup_unique]
    rfl
  · have : ¬ ((2 : Fin 3) ∈ ({0, 1} : Set (Fin 3))) := by decide
    simp only [Fin.reduceFinMk, this, if_true]
    exact Real.iSup_of_isEmpty _

theorem T'_line (c : ℝ) (x : Bool) :
    T' M0 (fun y => c * bb y) x = max 0 (c / 2 - 1) * bb x := by
  unfold T'
  simp only [inner_eq]
  have hbdd : BddAbove (Set.range fun k : Fin 3 =>
      if k = 2 then (0 : ℝ) else rr (x, k) + 1 / 2 * (c * bb (gg (x, k)))) :=
    (Set.finite_range _).bddAbove
  rw [max_mul_of_nonneg _ _ (bb_pos x).le, zero_mul]
  apply le_antisymm
  · refine ciSup_le fun k => ?_
    fin_cases k <;> cases x <;> simp [rr, gg, bb] <;>
      first | (right; linarith) | (left; linarith) | skip
    all_goals (rcases le_total (c / 2 - 1) 0 with h | h <;> [left; right] <;> nlinarith)
  · refine max_le (le_trans (by simp) (le_ciSup hbdd 2)) ?_
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd 0)
    cases x <;> simp [rr, gg, bb] <;> ring

end LPCex

open LPCex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hb1 : ∀ x, 1 ≤ b x)
    (hαb : M.β * αb < 1) (IMs : Set (E → ℝ)) (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (hTmaps : ∀ v ∈ IMs, (fun x => T' M v x) ∈ IMs) (Δ : Set (E → A))
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤),
    (∃ vstar ∈ IMs, (∀ x, Jinf M x = (vstar x : EReal)) ∧ vstar ∈ ZP M IMs ∧
        ((∫ x, vstar x ∂p : ℝ) : EReal) = valP M IMs p ∧
        valP M IMs p = valD M b IMs p) ∧
      (∃ μstar ∈ ZD M b IMs p, ∃ fstar : E → A, IsMaximizerOf M (Jinf M) fstar ∧
        valD M b IMs p = ((∫ xa, M.r xa ∂μstar : ℝ) : EReal) ∧
        valD M b IMs p = erealIntegral p (fun x => Jinfpi M M.r (fun _ => fstar) x) ∧
        IsPOptimal M p (fun _ => fstar))) := by
  intro h
  have hb : IsBoundingFunction M0 bb 2 1 :=
    { hb_meas := Measurable.of_discrete
      hb_nonneg := fun x => (bb_pos x).le
      hcr := by norm_num
      hαb := by norm_num
      hr := fun xa _ => by
        obtain ⟨x, k⟩ := xa
        cases x <;> fin_cases k <;> simp [M0, rr, bb] <;> norm_num
      hQ := fun xa hxa => by
        obtain ⟨x, k⟩ := xa
        rw [Q_eq, lintegral_dirac]
        apply ENNReal.ofReal_le_ofReal
        cases x <;> fin_cases k <;> simp [gg, bb] }
  have hIM : IsClosedSubspaceOf bb IMs := by
    refine ⟨?_, ⟨0, by funext x; simp⟩, ?_, ?_, ?_⟩
    · rintro v ⟨c, rfl⟩
      refine ⟨Measurable.of_discrete, |c|, abs_nonneg _, fun x => ?_⟩
      rw [abs_mul, abs_of_pos (bb_pos x)]
    · rintro v ⟨c, rfl⟩ w ⟨d, rfl⟩
      exact ⟨c + d, by funext x; simp; ring⟩
    · rintro e v ⟨c, rfl⟩
      exact ⟨e * c, by funext x; simp; ring⟩
    · intro vn v hvn _ hlim
      choose c hc using hvn
      have key : ∀ x, Filter.Tendsto c Filter.atTop (nhds (v x / bb x)) := by
        intro x
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
        have hle : |vn n x - v x| / bb x ≤ normb bb (fun x => vn n x - v x) :=
          le_ciSup (f := fun x => |vn n x - v x| / bb x) (Set.finite_range _).bddAbove x
        refine le_trans (le_of_eq ?_) hle
        rw [hc n, Real.norm_eq_abs]
        have hb := bb_pos x
        rw [← abs_of_pos hb, ← abs_div, abs_of_pos hb]
        congr 1
        field_simp
      have e := tendsto_nhds_unique (key true) (key false)
      refine ⟨v true / bb true, ?_⟩
      funext x
      cases x
      · rw [e]; field_simp [(bb_pos false).ne']
      · field_simp [(bb_pos true).ne']
  have hTm : ∀ v ∈ IMs, (fun x => T' M0 v x) ∈ IMs := by
    rintro v ⟨c, rfl⟩
    exact ⟨max 0 (c / 2 - 1), by funext x; exact T'_line c x⟩
  have hmax : ∀ v ∈ IMs, ∃ f ∈ (Set.univ : Set (Bool → Fin 3)),
      IsMaximizerOf M0 (fun x => (v x : EReal)) f := by
    rintro v ⟨c, rfl⟩
    refine ⟨fun x => if x then 0 else (if 2 ≤ c then 0 else 1), Set.mem_univ _,
      ⟨Measurable.of_discrete, fun x => by cases x <;> split_ifs <;> simp [M0]⟩, ?_⟩
    have hL : ∀ x k, L M0 (fun y => ((c * bb y : ℝ) : EReal)) (x, k) =
        ((rr (x, k) + 1 / 2 * (c * bb (gg (x, k))) : ℝ) : EReal) := by
      intro x k
      unfold L
      rw [Q_eq, eI_dirac, ← EReal.coe_mul, ← EReal.coe_add]
      rfl
    funext x
    unfold T
    rw [Dx_eq, iSup_insert, iSup_singleton, hL, hL, hL, ← EReal.coe_strictMono.monotone.map_max]
    congr 1
    cases x
    · by_cases hc : 2 ≤ c
      · simp [hc, rr, gg, bb]; linarith
      · simp [hc, rr, gg, bb]; linarith
    · simp [rr, gg, bb]
  have hpb : ∫⁻ x, ENNReal.ofReal (bb x) ∂(Measure.dirac true) < ⊤ := by
    rw [lintegral_dirac]; exact ENNReal.ofReal_lt_top
  obtain ⟨⟨vstar, ⟨c, rfl⟩, hJ, _⟩, _⟩ := h M0 bb 2 1 hb
    (fun x => by cases x <;> simp [bb]) (by show (1 / 2 : ℝ) * 1 < 1; norm_num) IMs hIM
    ⟨1, by funext x; simp⟩ hTm Set.univ hmax (Measure.dirac true) hpb
  have h1 := Jinf_true_le
  have h2 := Jinf_false_ge
  rw [hJ] at h1 h2
  have h1' : c * bb true ≤ -3 / 2 := EReal.coe_le_coe_iff.mp h1
  have h2' : -2 ≤ c * bb false := EReal.coe_le_coe_iff.mp h2
  simp [bb] at h1' h2'
  linarith

#print axioms solution

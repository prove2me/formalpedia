-- Prove2me | solution 1 for MDPFinance.Stationary.structure_theorem_stationary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:09:43.601772+00:00
-- url     : https://prove2.me/submissions/57a5e667-425d-4798-a63b-e395a2e72619

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators
import Definitions.Def_MDPFinance_Stationary_StructureAssumption
import Definitions.Def_MDPFinance_Stationary_ValueFunction

open MeasureTheory ProbabilityTheory
open MDPFinance.Stationary

namespace StrStatAux

lemma pp (r : ℝ) : ((r : EReal) ⊔ 0).toENNReal = ENNReal.ofReal r := by
  rcases le_total r 0 with h | h
  · have : (r : EReal) ⊔ 0 = 0 := sup_of_le_right (by exact_mod_cast h)
    rw [this, ENNReal.ofReal_of_nonpos h]; simp
  · have : (r : EReal) ⊔ 0 = r := sup_of_le_left (by exact_mod_cast h)
    rw [this, EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

lemma ereal_mono {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ a, v a ≤ w a) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add ?_ ?_
  · exact_mod_cast lintegral_mono (fun a => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h a) 0))
  · rw [EReal.neg_le_neg_iff]
    exact_mod_cast lintegral_mono (fun a => EReal.toENNReal_le_toENNReal
      (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h a)) 0))

lemma ennreal_ereal_sub (A B : ENNReal) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    (A : EReal) + -(B : EReal) = ((A.toReal - B.toReal : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB]
  norm_cast

lemma meas_toENNReal : Measurable EReal.toENNReal :=
  (show Monotone EReal.toENNReal from fun _ _ h => EReal.toENNReal_le_toENNReal h).measurable

lemma meas_neg : Measurable (fun y : EReal => -y) := (continuous_neg (G := EReal)).measurable

/-- pointwise: positive part of `c + k` -/
lemma pos_le (c : ℝ) (k : EReal) :
    ((((c : EReal) + k) ⊔ 0).toENNReal) ≤ ENNReal.ofReal c + (k ⊔ 0).toENNReal := by
  induction k using EReal.rec with
  | bot => simp
  | top => simp
  | coe y =>
    rw [← EReal.coe_add, pp, pp]; exact ENNReal.ofReal_add_le

lemma pos_le' (c : ℝ) (k : EReal) :
    (k ⊔ 0).toENNReal ≤ ENNReal.ofReal (-c) + ((((c : EReal) + k) ⊔ 0).toENNReal) := by
  have h := pos_le (-c) ((c : EReal) + k)
  have e : ((-c : ℝ) : EReal) + ((c : EReal) + k) = k := by
    rw [← add_assoc, ← EReal.coe_add]; simp
  rwa [e] at h

lemma neg_eq (c : ℝ) (k : EReal) : -((c : EReal) + k) = ((-c : ℝ) : EReal) + -k := by
  induction k using EReal.rec with
  | bot => simp
  | top => simp
  | coe y => rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, ← EReal.coe_add]; congr 1; ring

lemma ident (c : ℝ) (k : EReal) :
    (((c : EReal) + k) ⊔ 0).toENNReal + ((-k) ⊔ 0).toENNReal + ENNReal.ofReal (-c) =
      ((-((c : EReal) + k)) ⊔ 0).toENNReal + (k ⊔ 0).toENNReal + ENNReal.ofReal c := by
  induction k using EReal.rec with
  | bot => simp
  | top => simp
  | coe y =>
    rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, pp, pp, pp, pp]
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_ofReal']
    simp only [max_def]
    split_ifs <;> linarith

lemma ereal_shift {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c : ℝ) (k : α → EReal) (hk : Measurable k) :
    erealIntegral μ (fun w => (c : EReal) + k w) = (c : EReal) + erealIntegral μ k := by
  unfold erealIntegral
  set A := ∫⁻ w, (k w ⊔ 0).toENNReal ∂μ
  set B := ∫⁻ w, ((-k w) ⊔ 0).toENNReal ∂μ
  set A' := ∫⁻ w, (((c : EReal) + k w) ⊔ 0).toENNReal ∂μ
  set B' := ∫⁻ w, ((-((c : EReal) + k w)) ⊔ 0).toENNReal ∂μ
  have mA : Measurable fun w => (k w ⊔ 0).toENNReal :=
    meas_toENNReal.comp (hk.sup measurable_const)
  have mB : Measurable fun w => ((-k w) ⊔ 0).toENNReal :=
    meas_toENNReal.comp ((meas_neg.comp hk).sup measurable_const)
  have mck : Measurable fun w => (c : EReal) + k w := measurable_const.add hk
  have mA' : Measurable fun w => (((c : EReal) + k w) ⊔ 0).toENNReal :=
    meas_toENNReal.comp (mck.sup measurable_const)
  have mB' : Measurable fun w => ((-((c : EReal) + k w)) ⊔ 0).toENNReal :=
    meas_toENNReal.comp ((meas_neg.comp mck).sup measurable_const)
  have h1 : A' ≤ ENNReal.ofReal c + A := by
    calc A' ≤ ∫⁻ w, (ENNReal.ofReal c + (k w ⊔ 0).toENNReal) ∂μ :=
          lintegral_mono (fun w => pos_le c (k w))
      _ = ENNReal.ofReal c + A := by
          rw [lintegral_add_left measurable_const]
          simp only [lintegral_const, measure_univ, mul_one]; rfl
  have h2 : A ≤ ENNReal.ofReal (-c) + A' := by
    calc A ≤ ∫⁻ w, (ENNReal.ofReal (-c) + (((c : EReal) + k w) ⊔ 0).toENNReal) ∂μ :=
          lintegral_mono (fun w => pos_le' c (k w))
      _ = ENNReal.ofReal (-c) + A' := by
          rw [lintegral_add_left measurable_const]
          simp only [lintegral_const, measure_univ, mul_one]; rfl
  have h3 : B' ≤ ENNReal.ofReal (-c) + B := by
    calc B' ≤ ∫⁻ w, (ENNReal.ofReal (-c) + ((-k w) ⊔ 0).toENNReal) ∂μ :=
          lintegral_mono (fun w => by rw [neg_eq]; exact pos_le (-c) (-k w))
      _ = ENNReal.ofReal (-c) + B := by
          rw [lintegral_add_left measurable_const]
          simp only [lintegral_const, measure_univ, mul_one]; rfl
  have h4 : B ≤ ENNReal.ofReal c + B' := by
    calc B ≤ ∫⁻ w, (ENNReal.ofReal c + ((-((c : EReal) + k w)) ⊔ 0).toENNReal) ∂μ :=
          lintegral_mono (fun w => by rw [neg_eq]; simpa using pos_le' (-c) (-k w))
      _ = ENNReal.ofReal c + B' := by
          rw [lintegral_add_left measurable_const]
          simp only [lintegral_const, measure_univ, mul_one]; rfl
  have hid : A' + B + ENNReal.ofReal (-c) = B' + A + ENNReal.ofReal c := by
    have := lintegral_congr (μ := μ) (fun w => ident c (k w))
    rw [lintegral_add_right _ measurable_const, lintegral_add_right _ measurable_const,
      lintegral_add_left mA', lintegral_add_left mB'] at this
    simpa using this
  by_cases hA : A = ⊤
  · have hA' : A' = ⊤ := by
      by_contra h
      have : ENNReal.ofReal (-c) + A' ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, h⟩
      exact this (top_le_iff.1 (hA ▸ h2))
    by_cases hB : B = ⊤
    · have hB' : B' = ⊤ := by
        by_contra h
        have : ENNReal.ofReal c + B' ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, h⟩
        exact this (top_le_iff.1 (hB ▸ h4))
      rw [hA, hA', hB, hB']; simp
    · have hB' : B' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hB⟩) h3
      rw [hA, hA', ← EReal.coe_ennreal_toReal hB, ← EReal.coe_ennreal_toReal hB']
      simp only [EReal.coe_ennreal_top]
      rw [← EReal.coe_neg, ← EReal.coe_neg, EReal.top_add_coe, EReal.top_add_coe,
        EReal.coe_add_top]
  · have hA' : A' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hA⟩) h1
    by_cases hB : B = ⊤
    · have hB' : B' = ⊤ := by
        by_contra h
        have : ENNReal.ofReal c + B' ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, h⟩
        exact this (top_le_iff.1 (hB ▸ h4))
      rw [hB, hB', ← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hA']
      simp only [EReal.coe_ennreal_top, EReal.neg_top, EReal.add_bot]
    · have hB' : B' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hB⟩) h3
      rw [ennreal_ereal_sub _ _ hA' hB', ennreal_ereal_sub _ _ hA hB]
      norm_cast
      have := congrArg ENNReal.toReal hid
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hA', hB⟩) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hB', hA⟩) ENNReal.ofReal_ne_top,
        ENNReal.toReal_add hA' hB, ENNReal.toReal_add hB' hA,
        ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at this
      have hc : max c 0 - max (-c) 0 = c := by simp only [max_def]; split_ifs <;> linarith
      linarith

lemma pos_mul (d : ℝ) (hd : 0 < d) (k : EReal) :
    (((d : EReal) * k) ⊔ 0).toENNReal = ENNReal.ofReal d * (k ⊔ 0).toENNReal := by
  induction k using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hd]
  | top => simp [EReal.coe_mul_top_of_pos hd, ENNReal.mul_top (ENNReal.ofReal_pos.2 hd).ne']
  | coe y => rw [← EReal.coe_mul, pp, pp, ENNReal.ofReal_mul hd.le]

lemma ereal_smul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (d : ℝ) (hd : 0 < d) (k : α → EReal) :
    erealIntegral μ (fun w => (d : EReal) * k w) = (d : EReal) * erealIntegral μ k := by
  unfold erealIntegral
  have e1 : ∀ w, ((-((d : EReal) * k w)) ⊔ 0).toENNReal = ENNReal.ofReal d * ((-k w) ⊔ 0).toENNReal := by
    intro w; rw [← mul_neg]; exact pos_mul d hd _
  simp_rw [pos_mul d hd, e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hd.le) (EReal.coe_ne_top d)]
  simp only [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hd.le, mul_neg]

lemma ereal_affine {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (c d : ℝ) (hd : 0 < d) (k : α → EReal) (hk : Measurable k) :
    erealIntegral μ (fun w => (c : EReal) + (d : EReal) * k w) =
      (c : EReal) + (d : EReal) * erealIntegral μ k := by
  rw [ereal_shift μ c _ (hk.const_mul _), ereal_smul μ d hd]

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma int_meas (M : StationaryMarkovDecisionModel E A) {f : E → A} (hf : Measurable f)
    {v : E → EReal} (hv : Measurable v) :
    Measurable (fun x => erealIntegral (M.Q (x, f x)) v) := by
  unfold erealIntegral
  have hQ : Measurable (fun x => M.Q (x, f x)) :=
    M.Q.measurable.comp (measurable_id.prodMk hf)
  have h1 : Measurable (fun x => ∫⁻ a, (v a ⊔ 0).toENNReal ∂(M.Q (x, f x))) :=
    (Measure.measurable_lintegral (meas_toENNReal.comp (hv.sup measurable_const))).comp hQ
  have h2 : Measurable (fun x => ∫⁻ a, ((-v a) ⊔ 0).toENNReal ∂(M.Q (x, f x))) :=
    (Measure.measurable_lintegral (meas_toENNReal.comp
      ((meas_neg.comp hv).sup measurable_const))).comp hQ
  exact (measurable_coe_ennreal_ereal.comp h1).add (meas_neg.comp (measurable_coe_ennreal_ereal.comp h2))

lemma L_meas (M : StationaryMarkovDecisionModel E A) {f : E → A} (hf : Measurable f)
    {v : E → EReal} (hv : Measurable v) :
    Measurable (fun x => L M v (x, f x)) := by
  unfold L
  exact (measurable_coe_real_ereal.comp (M.hr_meas.comp (measurable_id.prodMk hf))).add
    ((int_meas M hf hv).const_mul _)

/-- Combined measurability and affine-shift lemma for `EFromToAcc`. -/
lemma eft (M : StationaryMarkovDecisionModel E A) (k : ℕ) :
    ∀ π : ℕ → E → A, (∀ j < k, Measurable (π j)) →
      Measurable (fun x => EFromToAcc M π (fun x => (M.g x : EReal)) k x 0 1) ∧
      ∀ x (a d : ℝ), 0 < d → EFromToAcc M π (fun x => (M.g x : EReal)) k x a d =
        (a : EReal) + (d : EReal) * EFromToAcc M π (fun x => (M.g x : EReal)) k x 0 1 := by
  induction k with
  | zero =>
    intro π _
    refine ⟨?_, ?_⟩
    · simp only [EFromToAcc, EReal.coe_one, one_mul, zero_add]
      exact measurable_coe_real_ereal.comp M.hg_meas
    · intro x a d _
      simp [EFromToAcc]
  | succ k ih =>
    intro π hπ
    have hprob : ∀ xa, IsProbabilityMeasure (M.Q xa) := M.hQ_prob
    obtain ⟨ihm, iha⟩ := ih (fun j => π (j + 1)) (fun j hj => hπ (j + 1) (by omega))
    have key : ∀ x (a d : ℝ), 0 < d → EFromToAcc M π (fun x => (M.g x : EReal)) (k + 1) x a d =
        ((a + d * M.r (x, π 0 x) : ℝ) : EReal) + ((d * M.β : ℝ) : EReal) *
          erealIntegral (M.Q (x, π 0 x))
            (fun x' => EFromToAcc M (fun j => π (j + 1)) (fun x => (M.g x : EReal)) k x' 0 1) := by
      intro x a d hd
      rw [EFromToAcc]
      have hacc : (a : EReal) + (d : EReal) * (M.r (x, π 0 x) : EReal) =
          ((a + d * M.r (x, π 0 x) : ℝ) : EReal) := by norm_cast
      rw [hacc]
      have hdb : 0 < d * M.β := mul_pos hd M.hβ_pos
      simp_rw [iha _ _ _ hdb]
      exact ereal_affine _ _ _ hdb _ ihm
    have key0 : ∀ x, EFromToAcc M π (fun x => (M.g x : EReal)) (k + 1) x 0 1 =
        L M (fun x' => EFromToAcc M (fun j => π (j + 1)) (fun x => (M.g x : EReal)) k x' 0 1)
          (x, π 0 x) := by
      intro x
      have := key x 0 1 one_pos
      simp only [EReal.coe_zero, zero_add, one_mul] at this
      rw [this, L]
    refine ⟨?_, ?_⟩
    · simp_rw [key0]
      exact L_meas M (hπ 0 (by omega)) ihm
    · intro x a d hd
      rw [key x a d hd, key0 x, L]
      rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hd.le) (EReal.coe_ne_top d),
        ← add_assoc, ← mul_assoc]
      norm_cast

lemma Jpi_succ (M : StationaryMarkovDecisionModel E A) (π : ℕ → E → A) (k : ℕ)
    (hπ : ∀ j < k + 1, Measurable (π j)) :
    Jpi M π (k + 1) = Tf M (Jpi M (fun j => π (j + 1)) k) (π 0) := by
  have hprob : ∀ xa, IsProbabilityMeasure (M.Q xa) := M.hQ_prob
  obtain ⟨ihm, iha⟩ := eft M k (fun j => π (j + 1)) (fun j hj => hπ (j + 1) (by omega))
  funext x
  unfold Jpi Tf L
  rw [EFromToAcc]
  have hacc : ((0 : EReal)) + ((1 : ℝ) : EReal) * (M.r (x, π 0 x) : EReal) =
      ((M.r (x, π 0 x) : ℝ) : EReal) := by simp
  rw [hacc, one_mul]
  simp_rw [iha _ _ _ M.hβ_pos]
  exact ereal_affine _ _ _ M.hβ_pos _ ihm

lemma L_mono (M : StationaryMarkovDecisionModel E A) {v w : E → EReal} (h : ∀ x, v x ≤ w x)
    (xa : E × A) : L M v xa ≤ L M w xa := by
  unfold L
  gcongr
  · exact_mod_cast M.hβ_pos.le
  · exact ereal_mono _ h

lemma upper (M : StationaryMarkovDecisionModel E A) (k : ℕ) :
    ∀ π : ℕ → E → A, IsPolicySeq M k π → ∀ x,
      Jpi M π k x ≤ TChain M k (fun x => (M.g x : EReal)) x := by
  induction k with
  | zero => intro π _ x; simp [Jpi, EFromToAcc, TChain]
  | succ k ih =>
    intro π hπ x
    rw [Jpi_succ M π k (fun j hj => (hπ j hj).1)]
    have ih' := ih (fun j => π (j + 1)) (fun j hj => hπ (j + 1) (by omega))
    calc Tf M (Jpi M (fun j => π (j + 1)) k) (π 0) x
        ≤ L M (TChain M k (fun x => (M.g x : EReal))) (x, π 0 x) := L_mono M ih' _
      _ ≤ T M (TChain M k (fun x => (M.g x : EReal))) x :=
          le_iSup₂ (f := fun a (_ : a ∈ M.Dx x) => L M _ (x, a)) (π 0 x) ((hπ 0 (by omega)).2 x)

lemma chain (M : StationaryMarkovDecisionModel E A) (k : ℕ) :
    ∀ fs : ℕ → E → A, (∀ m, 1 ≤ m → m ≤ k →
      IsMaximizer M (TChain M (m - 1) (fun x => (M.g x : EReal))) (fs m)) →
      Jpi M (fun j => fs (k - j)) k = TChain M k (fun x => (M.g x : EReal)) := by
  induction k with
  | zero => intro fs _; funext x; simp [Jpi, EFromToAcc, TChain]
  | succ k ih =>
    intro fs hfs
    rw [Jpi_succ M _ k (fun j hj => (hfs (k + 1 - j) (by omega) (by omega)).1.1)]
    have htail : (fun j => fs (k + 1 - (j + 1))) = fun j => fs (k - j) := by
      funext j; congr 1; omega
    simp only [htail, Nat.sub_zero]
    rw [ih fs (fun m h1 h2 => hfs m h1 (by omega))]
    have := (hfs (k + 1) (by omega) le_rfl).2
    exact this

end StrStatAux

theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : StationaryMarkovDecisionModel E A) (IMs : Set (E → EReal)) (Delta : Set (E → A))
    (hSAN : StructureAssumption M IMs Delta) (N : ℕ) (_hAN : IntegrabilityAssumption M N) :
    (∀ n ≤ N, J M n ∈ IMs) ∧
      (∀ n, 1 ≤ n → n ≤ N → J M n = T M (J M (n - 1))) ∧
      (∀ n ≤ N, J M n = TChain M n (fun x => (M.g x : EReal))) ∧
      (∀ n, 1 ≤ n → n ≤ N → ∃ f ∈ Delta, IsMaximizer M (J M (n - 1)) f) ∧
      (∀ fstar : ℕ → E → A, (∀ n, 1 ≤ n → n ≤ N → IsMaximizer M (J M (n - 1)) (fstar n)) →
        Jpi M (fun k => fstar (N - k)) N = J M N) := by
  obtain ⟨_, hDel, hg, hT, hmax⟩ := hSAN
  set g : E → EReal := fun x => (M.g x : EReal) with hgdef
  have mem : ∀ n, TChain M n g ∈ IMs := by
    intro n
    induction n with
    | zero => exact hg
    | succ n ih => exact hT _ ih
  have hJ : ∀ n, J M n = TChain M n g := by
    intro n
    choose fs hfsD hfs using fun m => hmax _ (mem (m - 1))
    have hpol : IsPolicySeq M n (fun j => fs (n - j)) := fun j _ => (hfs _).1
    have hc := StrStatAux.chain M n fs (fun m _ _ => hfs m)
    funext x
    apply le_antisymm
    · exact iSup₂_le fun π hπ => StrStatAux.upper M n π hπ x
    · rw [← hc]
      exact le_iSup₂ (f := fun π (_ : π ∈ {π | IsPolicySeq M n π}) => Jpi M π n x) _ hpol
  refine ⟨fun n _ => hJ n ▸ mem n, ?_, fun n _ => hJ n, ?_, ?_⟩
  · intro n h1 _
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hJ, hJ]; rfl
  · intro n _ _
    rw [hJ]; exact hmax _ (mem _)
  · intro fstar hf
    rw [hJ]
    exact StrStatAux.chain M N fstar (fun m h1 h2 => hJ (m - 1) ▸ hf m h1 h2)

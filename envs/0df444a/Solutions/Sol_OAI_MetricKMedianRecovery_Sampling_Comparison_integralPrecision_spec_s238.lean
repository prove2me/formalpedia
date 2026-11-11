-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:41.744103+00:00
-- url     : https://prove2.me/submissions/20232f39-73c7-4292-bcd7-dcff07bb4cf3

import Mathlib
import Definitions.Def_Q238K027

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FirstSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma thirdNormalizer_lt_one (J : ℕ) : thirdNormalizer J < 1 := by
  rw [thirdNormalizer_eq]
  have hh : (0 : ℝ) < (1/2 : ℝ)^J := pow_pos (by norm_num) _
  linarith

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PrecisionBits
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma menuWeight_uniform_lower (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (e : Fin M ⊕ (Fin (E+1) ⊕ Fin J)) :
    1 / (3*((M:ℝ)+E+1)*2^J) ≤ menuWeight M E J e := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hQ : (0:ℝ) < (M:ℝ)+E+1 := by positivity
  have hpow : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
  rcases e with i | (i | i)
  · simp only [menuWeight]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · simp only [menuWeight]
    apply one_div_le_one_div_of_le (by positivity)
    have hE : (0:ℝ) ≤ E := by positivity
    nlinarith
  · simp only [menuWeight]
    have hi : i.val+1 ≤ J := i.isLt
    have hp : (1/2:ℝ)^J ≤ (1/2:ℝ)^(i.val+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
    have ht := thirdNormalizer_pos hJ
    have ht1 := (thirdNormalizer_lt_one J).le
    have hu : (1/2:ℝ)^J ≤ (1/2:ℝ)^(i.val+1)/thirdNormalizer J := by
      apply (le_div_iff₀ ht).mpr
      exact (mul_le_of_le_one_right (by positivity) ht1).trans hp
    calc
      1/(3*((M:ℝ)+E+1)*2^J) = (1/(3*((M:ℝ)+E+1)))*(1/2:ℝ)^J := by
        rw [one_div_pow]
        simp only [one_div,mul_inv_rev]
        ring
      _ ≤ (1/3:ℝ)*(1/2:ℝ)^J := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply one_div_le_one_div_of_le (by norm_num)
        have hsum : (1:ℝ) ≤ (M:ℝ)+E+1 := by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) E]
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (by norm_num)

lemma precision_power (n d M E J : ℕ) :
    12*(n:ℝ)*d*((M:ℝ)+E+1)*2^J ≤ (2:ℝ)^(precisionBits n d M E J) := by
  have hn : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hd : (d:ℝ) ≤ (2:ℝ)^d := by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
  have hq : (M:ℝ)+E+1 ≤ (2:ℝ)^(M+E+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := M+E+1)).le
  calc
    12*(n:ℝ)*d*((M:ℝ)+E+1)*2^J ≤ 16*(2:ℝ)^n*2^d*2^(M+E+1)*2^J := by
      gcongr
      norm_num
    _ = (2:ℝ)^(precisionBits n d M E J) := by
      simp only [precisionBits,pow_add,pow_one]
      ring

end MetricKMedianRecovery.RadiusMenus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma real_mem_tags (S : Finset V) (s : State V) (v : V) :
    realTag v ∈ tags S s ↔ v ∈ S \ s.deleted := by
  simp [tags, realTag, leafTag]

omit [PseudoMetricSpace V] in
lemma leaf_mem_tags (S : Finset V) (s : State V) (j : ℕ) :
    leafTag j ∈ tags S s ↔ j ≤ s.leaves.length := by
  simp [tags, realTag, leafTag]

lemma chosen_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    chosen S Δ s x ∈ tags S s :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).1

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

lemma reference_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) : reference S Δ s x ≤ tagDistance Δ s x t :=
  Prod.Lex.monotone_fst _ _ (chosen_key_le S Δ s x ht)

lemma reference_le_diameter (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x ≤ Δ :=
  reference_le S Δ s x ((leaf_mem_tags S s 0).mpr (Nat.zero_le _))

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BlindUpdate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Precision
open RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma good_initial : Good (some (State.initial : State V)) := by
  intro s hs
  cases Option.some.inj hs
  simp [State.initial]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma good_retain (m : ℕ) (s : State V) (hs : ∀ z ∈ s.leaves, (1:ℝ) ≤ z.2) :
    Good (retain m s) := by
  intro t ht
  unfold retain at ht
  split_ifs at ht
  cases Option.some.inj ht
  exact hs

lemma good_update (D F S : Finset V) (hD : D.Nonempty) (Δ P kappa : ℝ)
    (m M E J : ℕ) (s : Option (State V)) (a : Action D M E J)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) (hs : Good s) :
    Good (update D F S hD Δ P kappa m M E J s a) := by
  cases s with
  | none => simp only [update,Good,reduceCtorEq,IsEmpty.forall_iff,implies_true]
  | some s =>
    have hrad := hs s rfl
    simp only [update]
    split_ifs with hw
    · rcases a with u | (w | ⟨w,e⟩)
      · simp [Good]
      · cases he : ofLex (chosen S Δ s w) with
        | inl v =>
          simp only [he]
          apply good_retain
          simpa only [State.remove] using hrad
        | inr j => simp [he,Good]
      · cases hr : menuRadius D hD P kappa m M E J s w e with
        | none => simp [hr,Good]
        | some R =>
          simp only [hr]
          split_ifs with hb
          · apply good_retain
            obtain ⟨f,hf⟩ := hb
            have hR := (hsep w w.property f (Finset.mem_filter.mp hf).1).trans
              (Finset.mem_filter.mp hf).2
            intro z hz
            simp only [State.add,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
            rcases hz with hz | hz
            · exact hrad z hz
            · simpa only [hz] using hR
          · simp [Good]
    · simp [Good]

lemma client_lower (D F S : Finset V) (hSF : S ⊆ F) (Δ : ℝ) (hΔ : 1 ≤ Δ)
    (s : State V) (hs : ∀ z ∈ s.leaves, (1:ℝ) ≤ z.2)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (w : V) (hw : w ∈ D) : 1 ≤ clientWeight S Δ s w := by
  apply le_trans _ (le_max_right _ _)
  unfold reference tagDistance
  have hc := chosen_mem S Δ s w
  cases he : ofLex (chosen S Δ s w) with
  | inl v =>
    have hc' : v ∈ S \ s.deleted := by
      apply (real_mem_tags S s v).mp
      simpa only [realTag,← he,toLex_ofLex] using hc
    exact hsep w hw v (hSF (Finset.mem_sdiff.mp hc').1)
  | inr j =>
    cases j with
    | zero => exact hΔ
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simpa only [hz] using hΔ
      | some z =>
        have hzmem : z ∈ s.leaves := List.mem_of_getElem? hz
        simpa only [hz] using (hs z hzmem).trans
          (le_add_of_nonneg_left (dist_nonneg : 0 ≤ dist w z.1))

lemma total_upper (D S : Finset V) (Δ : ℝ) (hΔ : 0 ≤ Δ) (s : State V) :
    totalWeight D S Δ s ≤ (D.card:ℝ)*Δ := by
  unfold totalWeight
  calc
    ∑ w ∈ D, clientWeight S Δ s w ≤ ∑ _w ∈ D, Δ := by
      apply Finset.sum_le_sum
      intro w _
      exact max_le hΔ (reference_le_diameter S Δ s w)
    _ = (D.card:ℝ)*Δ := by simp

end MetricKMedianRecovery.Sampling.Precision

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_OneStepLower
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Precision
open RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

lemma one_step_lower (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ : ℝ) (hΔ : 1 ≤ Δ) (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (s : Option (State V)) (hs : Good s)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (a : Action D M E J) (hp : 0 < transitionWeight D S Δ M E J s a) :
    1/(6*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J) ≤ transitionWeight D S Δ M E J s a := by
  let A : ℝ := 2*(D.card:ℝ)*Δ
  let B : ℝ := 3*((M:ℝ)+E+1)*2^J
  have hn : (1:ℝ) ≤ D.card := by exact_mod_cast hD.card_pos
  have hA : 0 < A := by dsimp [A] <;> positivity
  have hA1 : 1 ≤ A := by dsimp [A] <;> nlinarith
  have hQ : (1:ℝ) ≤ (M:ℝ)+E+1 := by
    linarith [Nat.cast_nonneg (α := ℝ) M,Nat.cast_nonneg (α := ℝ) E]
  have hB : 0 < B := by dsimp [B] <;> positivity
  have hB1 : 1 ≤ B := by
    have hpow : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
    dsimp [B]
    nlinarith
  have hAB : A*B = 6*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J := by dsimp [A,B] <;> ring
  have hOne : 1/(A*B) ≤ (1:ℝ) := by
    apply (div_le_iff₀ (mul_pos hA hB)).mpr
    nlinarith
  rw [← hAB]
  cases s with
  | none =>
    by_cases ha : a = Sum.inl ()
    · simpa only [transitionWeight,ite_eq_left ha] using hOne
    · simp only [transitionWeight,ite_eq_right ha,lt_self_iff_false] at hp
  | some s =>
    by_cases hw : 0 < totalWeight D S Δ s
    · have hR (w : D) : 1/A ≤ clientWeight S Δ s w/(2*totalWeight D S Δ s) := by
        apply (div_le_div_iff₀ hA (by positivity)).mpr
        have hh := client_lower D F S hSF Δ hΔ s (hs s rfl) hsep w w.property
        have ht := total_upper D S Δ (by linarith) s
        dsimp [A]
        nlinarith
      rcases a with u | (w | ⟨w,e⟩)
      · simp only [transitionWeight,ite_eq_left hw,lt_self_iff_false] at hp
      · simp only [transitionWeight,ite_eq_left hw]
        apply le_trans _ (hR w)
        apply one_div_le_one_div_of_le hA
        nlinarith
      · simp only [transitionWeight,ite_eq_left hw]
        calc
          1/(A*B) = (1/A)*(1/B) := by simp only [one_div,mul_inv_rev] <;> ring
          _ ≤ _ := mul_le_mul (hR w) (menuWeight_uniform_lower M E J hM hJ e)
            (by positivity) (div_nonneg (le_max_left _ _) (by positivity))
    · by_cases ha : a = Sum.inl ()
      · simpa only [transitionWeight,ite_eq_right hw,ite_eq_left ha] using hOne
      · simp only [transitionWeight,ite_eq_right hw,ite_eq_right ha,lt_self_iff_false] at hp

lemma one_step_accuracy (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ : ℝ) (hΔ : 1 ≤ Δ) (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (s : Option (State V)) (hs : Good s)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f)
    (a : Action D M E J) (hp : 0 < transitionWeight D S Δ M E J s a) :
    2 ≤ (2:ℝ)^(precisionBits D.card (Nat.ceil Δ) M E J) *
      transitionWeight D S Δ M E J s a := by
  have hn : (0:ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hden : 0 < 6*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J := by positivity
  have hl := (div_le_iff₀ hden).mp
    (one_step_lower D F S hD hSF Δ hΔ M E J hM hJ s hs hsep a hp)
  have hu : 12*(D.card:ℝ)*Δ*((M:ℝ)+E+1)*2^J ≤
      (2:ℝ)^(precisionBits D.card (Nat.ceil Δ) M E J) := by
    apply le_trans _ (precision_power D.card (Nat.ceil Δ) M E J)
    gcongr
    exact Nat.le_ceil Δ
  have hm := mul_le_mul_of_nonneg_right hu hp.le
  nlinarith only [hl,hm]

lemma precise_every_history (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ P kappa : ℝ) (hΔ : 1 ≤ Δ) (m M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) (n : ℕ)
    (s : Option (State V)) (hs : Good s) :
    Precise (update D F S hD Δ P kappa m M E J) (actualKernel D S Δ M E J hM hJ)
      (precisionBits D.card (Nat.ceil Δ) M E J) n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih _ (good_update D F S hD Δ P kappa m M E J s a hsep hs)⟩
    exact one_step_accuracy D F S hD hSF Δ hΔ M E J hM hJ s hs hsep

end MetricKMedianRecovery.Sampling.Precision

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralPrecision
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling Precision
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

attribute [local instance] OAI.MetricKMedianRecovery.Sampling.Comparison.instDecidableEqAction_2
lemma integralPrecision_spec_s238_oai (D F S : Finset V) (hD : D.Nonempty) (hSF : S ⊆ F)
    (Δ P : ℝ) (hΔ : 1 ≤ Δ) (m : ℕ)
    (hsep : ∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) :
    Precise (blindUpdate D F S hD Δ P m) (mainActual D S Δ m)
      (integralPrecision D Δ m) (2*m) (some State.initial) := by
  exact precise_every_history D F S hD hSF Δ P mainKappa hΔ m _ _ _
    (by unfold firstSize; omega) (by unfold thirdSize; omega) hsep (2*m) _ good_initial

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238_oai.{u_1}

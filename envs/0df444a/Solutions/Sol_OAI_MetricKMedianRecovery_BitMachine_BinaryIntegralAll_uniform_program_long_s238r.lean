-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:24:28.338587+00:00
-- url     : https://prove2.me/submissions/0fdf999a-9e7f-4aa7-884a-01ad9dea2041

import Mathlib
import Definitions.Def_Q238L054
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralAll_finite_program_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Live
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryPhaseBound
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma limit_upper (v Z : ℝ) (hv : 0 < v) (hZ : 1 ≤ Z) :
    (limit v Z : ℝ) < Real.log Z / Real.log (1+v^2)+2 := by
  have hK : 1 < 1+v^2 := by nlinarith
  have hn : 0 ≤ Real.log Z / Real.log (1+v^2) :=
    div_nonneg (Real.log_nonneg hZ) (Real.log_pos hK).le
  have hc := Nat.ceil_lt_add_one hn
  simp only [limit,Nat.cast_add,Nat.cast_one]
  linarith

theorem polynomial_limit_bound (v M N C : ℝ) (p : ℕ)
    (hv : 0 < v) (hN : 3 ≤ N) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hupper : M ≤ C*N^p) :
    (3*limit v (M+8*N*M) : ℝ) <
      3*((Real.log (9*C)+(p+1)*Real.log N)/Real.log (1+v^2)+2) := by
  have hNp : 0 < N := by linarith
  have hCp : 0 < C := by linarith
  have hMp : 0 < M := by linarith
  have hZ : 1 ≤ M+8*N*M := by nlinarith
  have hupper' : M+8*N*M ≤ 9*C*N^(p+1) := by
    calc
      M+8*N*M = (1+8*N)*M := by ring
      _ ≤ (9*N)*(C*N^p) := by gcongr; nlinarith
      _ = 9*C*N^(p+1) := by rw [pow_succ]; ring
  have hlog := Real.log_le_log (by linarith : 0 < M+8*N*M) hupper'
  have hlogeq : Real.log (9*C*N^(p+1)) = Real.log (9*C)+(p+1)*Real.log N := by
    rw [Real.log_mul (mul_pos (by norm_num) hCp).ne' (pow_pos hNp _).ne',Real.log_pow]
    simp only [Nat.cast_add,Nat.cast_one]
  rw [hlogeq] at hlog
  have hK : 0 < Real.log (1+v^2) := Real.log_pos (by nlinarith)
  have hl := limit_upper v (M+8*N*M) hv hZ
  have hdiv := div_le_div_of_nonneg_right hlog hK.le
  linarith

end MetricKMedianRecovery.HistoryPhaseBound

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGapPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring

lemma strictnessGap_pos {T : ℝ} (hT : 0 < T) : 0 < strictnessGap T := by
  unfold strictnessGap
  positivity

end MetricKMedianRecovery.Surplus

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_IndexedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma countConstant_ge_ten : (10:ℝ) ≤ countConstant (1/100) := by
  unfold countConstant
  have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
  linarith only [hh]

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSlack
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ParameterBounds
open Filter

lemma exists_rational_slack (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ q : ℚ, 0 < q ∧ (q:ℝ) ≤ 1/12 ∧ (q:ℝ) ≤ c/1000 ∧
      (q:ℝ)^2 ≤ c/(6*(T+2)) := by
  have hb : 0 < c/(6*(T+2)) := by positivity
  have hm : 0 < min (1/12:ℝ) (min (c/1000) (Real.sqrt (c/(6*(T+2))))) :=
    lt_min (by norm_num) (lt_min (by positivity) (Real.sqrt_pos.2 hb))
  obtain ⟨q,hq0,hq⟩ := exists_rat_btwn hm
  have hqa := (lt_min_iff.mp hq).1
  have hqb := (lt_min_iff.mp (lt_min_iff.mp hq).2).1
  have hqc := (lt_min_iff.mp (lt_min_iff.mp hq).2).2
  refine ⟨q,by exact_mod_cast hq0,hqa.le,hqb.le,?_⟩
  nlinarith [Real.sq_sqrt hb.le]

lemma exists_size_threshold (c v : ℝ) (hc : 0 < c) (hv : 0 < v) :
    ∃ Nstar : ℕ, 1 ≤ Nstar ∧ ∀ N : ℕ, Nstar ≤ N →
      (N:ℝ)^2/(2:ℝ)^N ≤ v ∧ 2/(N:ℝ) ≤ c/200 := by
  have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ) < 2)).eventually
    (gt_mem_nhds hv)
  have h2 := (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < c/200))
  obtain ⟨Nstar,hN⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨max 1 Nstar,le_max_left _ _,?_⟩
  intro N h
  exact ⟨(hN N ((le_max_right _ _).trans h)).1.le,
    (hN N ((le_max_right _ _).trans h)).2.le⟩

end MetricKMedianRecovery.ParameterBounds

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling IntegralCandidates

lemma commonL_bound (v C : ℝ) (Nstar n M N p : ℕ) (hv : 0 < v)
    (hN : 1 ≤ N) (hn : n ≤ N) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hupper : (M:ℝ) ≤ C*((N:ℝ)+2)^p) :
    (commonL v Nstar n M : ℝ) < (Nstar:ℝ)+
      3*((Real.log (9*C)+(p+1)*Real.log ((N:ℝ)+2))/Real.log (1+v^2)+2)+3 := by
  have hN' : (3:ℝ) ≤ (N:ℝ)+2 := by exact_mod_cast (by omega : 3 ≤ N+2)
  have hn' : (n:ℝ) ≤ (N:ℝ)+2 := by exact_mod_cast (by omega : n ≤ N+2)
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hsmall : HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M) ≤
      HistoryPhaseBound.limit v ((M:ℝ)+8*((N:ℝ)+2)*M) := by
    unfold HistoryPhaseBound.limit
    gcongr
    · exact (Real.log_pos (by nlinarith : (1:ℝ) < 1+v^2)).le
  have hb := HistoryPhaseBound.polynomial_limit_bound v M ((N:ℝ)+2) C p hv hN' hC hM' hupper
  have hmax : max Nstar (3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M)+1)) ≤
      Nstar+3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M)+1) := by omega
  have hcast : (commonL v Nstar n M:ℝ) ≤ (Nstar:ℝ)+
      3*(HistoryPhaseBound.limit v ((M:ℝ)+8*((N:ℝ)+2)*M):ℝ)+3 := by
    dsimp only [commonL]
    exact_mod_cast hmax.trans (by omega : Nstar+3*(HistoryPhaseBound.limit v ((M:ℝ)+8*(n:ℝ)*M)+1) ≤
      Nstar+3*HistoryPhaseBound.limit v ((M:ℝ)+8*((N:ℝ)+2)*M)+3)
  linarith

lemma countBound_bound (L : ℕ) : (countBound L:ℝ) ≤
    (2+4*countConstant (1/100)/(gamma/16))*(L:ℝ)+1 := by
  have hC := PhaseSurplusProducer.countConstant_ge_ten
  have hq : 0 ≤ 4*countConstant (1/100)*(L:ℝ)/(gamma/16) := by
    apply div_nonneg
    · positivity
    · exact (div_pos gamma_pos_s238r (by norm_num)).le
  have hc := Nat.ceil_lt_add_one hq
  have hm : max (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊ ≤
      2*L+⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊ := by omega
  have hm' : (countBound L:ℝ) ≤ 2*(L:ℝ)+(⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊:ℝ) := by
    exact_mod_cast hm
  calc
    (countBound L:ℝ) ≤ 2*(L:ℝ)+(⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊:ℝ) := hm'
    _ ≤ 2*(L:ℝ)+(4*countConstant (1/100)*(L:ℝ)/(gamma/16)+1) := by linarith
    _ = _ := by ring

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma cap_pos (n : ℕ) (eps : ℝ) : 0 < cap n eps := by unfold cap; omega

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AffineLogBound
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LogPolynomial

lemma affine_log_bound (B D : ℝ) : ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 2 ≤ x →
    B+D*Real.log x ≤ A*Real.log x := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|B|/Real.log 2+|D|+1,by positivity,?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog0 : 0 ≤ Real.log x := (Real.log_nonneg (by linarith : 1 ≤ x))
  have hfirst : |B| ≤ (|B|/Real.log 2)*Real.log x := by
    calc
      _ = (|B|/Real.log 2)*Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  nlinarith [le_abs_self B,le_abs_self D,
    mul_le_mul_of_nonneg_right (le_abs_self D) hlog0]

end MetricKMedianRecovery.LogPolynomial

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PolynomialProduct
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly

open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies

lemma cap_polynomial (n N : ℕ) (h : n ≤ N) :
    Rounding.cap n (gamma/16) ≤ (⌈20/(gamma/16)⌉₊+2)*(N+2)^2 := by
  have he : 0 < gamma/16 := div_pos gamma_pos_s238r (by norm_num)
  have hn : (n:ℝ)^2 ≤ ((N:ℝ)+2)^2 := by
    have h' : (n:ℝ) ≤ N := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) N]
  have hc : ⌈20*(n:ℝ)^2/(gamma/16)⌉₊ ≤ ⌈20/(gamma/16)⌉₊*(N+2)^2 := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = (20/(gamma/16))*(n:ℝ)^2 := by ring
      _ ≤ (20/(gamma/16))*((N:ℝ)+2)^2 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _)
  have hb : 1 ≤ (N+2)^2 := one_le_pow₀ (by omega)
  unfold Rounding.cap
  nlinarith

end MetricKMedianRecovery.GlobalAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus GlobalAssembly
lemma bounded_count_log (v : ℚ) (Nstar : ℕ) (hv : 0 < v) :
    ∃ A : ℝ, 0 < A ∧ ∀ n N : ℕ, 1≤N → n≤N →
      (countBound (commonL v Nstar n (Rounding.cap n (gamma/16))):ℝ) ≤
        A*Real.log ((N:ℝ)+2) := by
  let C : ℕ := ⌈20/(gamma/16)⌉₊+2
  let B : ℝ := Nstar+3*Real.log (9*C)/Real.log (1+(v:ℝ)^2)+9
  let D : ℝ := 9/Real.log (1+(v:ℝ)^2)
  obtain ⟨A1,hA1,hfirst⟩ := LogPolynomial.affine_log_bound B D
  let R : ℝ := 2+4*Anchoring.countConstant (1/100)/(gamma/16)
  have hR : 0 ≤ R := by
    have := PhaseSurplusProducer.countConstant_ge_ten
    have := gamma_pos_s238r
    dsimp [R]
    positivity
  obtain ⟨A,hA,hsecond⟩ := LogPolynomial.affine_log_bound 1 (R*A1)
  refine ⟨A,hA,?_⟩
  intro n N hN hn
  have hCap := cap_polynomial n N hn
  have hbound := commonL_bound v C Nstar n
    (Rounding.cap n (gamma/16)) N 2
    (by exact_mod_cast hv) hN hn (by dsimp [C]; exact_mod_cast (by omega : 1 ≤ ⌈20/(gamma/16)⌉₊+2))
    (Rounding.cap_pos _ _) (by exact_mod_cast hCap)
  have hL : (commonL v Nstar n (Rounding.cap n (gamma/16)):ℝ) ≤
      A1*Real.log ((N:ℝ)+2) := by
    apply le_trans hbound.le
    have ht := hfirst ((N:ℝ)+2) (by linarith [Nat.cast_nonneg (α := ℝ) N])
    calc
      _ = B+D*Real.log ((N:ℝ)+2) := by dsimp only [B,D] <;> ring
      _ ≤ _ := ht
  have hC := countBound_bound (commonL v Nstar n (Rounding.cap n (gamma/16)))
  calc
    _ ≤ R*(commonL v Nstar n (Rounding.cap n (gamma/16)):ℝ)+1 := hC
    _ ≤ R*(A1*Real.log ((N:ℝ)+2))+1 := by gcongr
    _ = 1+(R*A1)*Real.log ((N:ℝ)+2) := by ring
    _ ≤ _ := hsecond _ (by linarith [Nat.cast_nonneg (α := ℝ) N])

attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus GlobalAssembly
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

theorem uniform_program_long_s238r_oai (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ)
    (_hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F : Finset (Fin n)) (k : ℕ)
    (_hD : D.Nonempty) (_hk : 0<k) (_hkF : k≤F.card)
    (_hbound : ∀ x,∀ f∈F,δ x f≤ Rounding.cap D.card (gamma/16))
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (g : List Bool) (_hg : D.card+F.card≤g.length),
    let M := Rounding.cap D.card (gamma/16)
    let N := D.card+F.card
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
    ∃ S : Finset (Fin n),
      (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
        BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
      (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤k ∧
        realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤5*optimum F D k) ∧
      (1-FailureBudget.failure gamma e N≤ probability
        (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
          (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
      average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
        ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k := by
  have hT : 0<200*countConstant (1/100) := by linarith [PhaseSurplusProducer.countConstant_ge_ten]
  have hstrict:=strictnessGap_pos hT
  obtain ⟨v,hv,hv1,hvc,hvs⟩:=ParameterBounds.exists_rational_slack _ _ hstrict hT
  have hvR : (0:ℝ)<v := by exact_mod_cast hv
  obtain ⟨Nstar,hNstar,hsize⟩:=ParameterBounds.exists_size_threshold _ _ hstrict hvR
  obtain ⟨A,_,hlog⟩:=bounded_count_log v Nstar hv
  let C : ℕ := ⌈1/v^2⌉₊
  have hv2 : (0:ℚ)<v^2 := sq_pos_of_pos hv
  have hC : 2≤(1+v^2)^C := by
    have ha : (1:ℚ)≤C*v^2 := (div_le_iff₀ hv2).mp (Nat.le_ceil _)
    have hb:=one_add_mul_le_pow (by linarith : (-2:ℚ)≤v^2) C
    linarith
  obtain ⟨Q,d,hQ⟩:=finite_program_s238r A e
  refine ⟨v,C,Q,d,?_⟩
  intro n _ δ hδ D F k hD hk hkF hbound hsep g hg
  dsimp only
  let M:=Rounding.cap D.card (gamma/16)
  let N:=D.card+F.card
  let L:=commonL v Nstar D.card M
  have hNL : Nstar≤L := le_max_left _ _
  have hL : 0<L := by omega
  have hlarge (hl:2*L<k) : Nstar≤N := by dsimp [N];omega
  exact hQ δ hδ D F k L M N C v hD hk hL hkF rfl (Rounding.cap_pos _ _) le_rfl
    hbound hsep hvR hv1 hvc hvs (fun hl=>(hsize _ (hlarge hl)).2)
    (fun hl=>(hsize _ (hlarge hl)).1) (le_max_right _ _) hC g hg (hlog D.card N (by dsimp [N];omega) (by dsimp [N];omega))
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.uniform_program_long_s238r_oai

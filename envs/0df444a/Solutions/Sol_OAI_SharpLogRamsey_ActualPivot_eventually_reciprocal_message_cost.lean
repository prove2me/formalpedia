-- Prove2me | solution 1 for OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:31:19.437545+00:00
-- url     : https://prove2.me/submissions/7698298e-340b-4fa3-99c7-07a3313fe90c

import Mathlib
import Definitions.Def_OAIQ045S000

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SharpLogRamsey.ScaleSelection
open Filter Real
open scoped Topology

theorem eventually_polynomial_exp_neg_rpow_lt (C a b c ε : ℝ)
    (hb : 0 < b) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a*Real.exp (-c*x^b) < ε := by
  have ht := (isLittleO_rpow_exp_pos_mul_atTop (a/b) hc).bound
    (show 0 < ε/(2*(|C|+1)) by positivity)
  have hcomp := (tendsto_rpow_atTop hb).eventually ht
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hp : (x^b)^(a/b) = x^a := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp,
    abs_of_pos (Real.rpow_pos_of_pos hx0 a)] at hx
  have hC : C ≤ |C|+1 := by linarith [le_abs_self C]
  calc
    _ ≤ (|C|+1)*x^a*Real.exp (-c*x^b) := by
      gcongr
    _ ≤ (|C|+1)*(ε/(2*(|C|+1))*Real.exp (c*x^b))*Real.exp (-c*x^b) := by
      gcongr
    _ = ε/2 := by
      rw [mul_assoc (|C|+1), mul_assoc, ← Real.exp_add,
        show c*x^b+-c*x^b=0 by ring, Real.exp_zero]
      field_simp
    _ < ε := by linarith

end SharpLogRamsey.ScaleSelection
end

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_TailSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

end
end SharpLogRamsey.HighRankExcess
end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Entropy_HighRankEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {K V Ω : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_bound {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Fintype.card (Projectivization K V):ℝ)≤2*(Nat.card K:ℝ)^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  simp only [Nat.cast_pow]
  exact HighRankExcess.geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)) d

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_positive {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (0:ℝ)<Fintype.card (Projectivization K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  apply lt_of_lt_of_le (by norm_num : (0:ℝ)<(Nat.card K^0:ℕ))
  exact single_le_sum (fun i _=>Nat.cast_nonneg _) (mem_range.mpr (by omega))

end
end SharpLogRamsey.ActualHighRank

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_RootCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real ActualHighRank ExecutedPotential TreeDecoder
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in
lemma projective_log_card_add_one {d : ℕ} (hdim : Module.finrank K V=d+1)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤((d:ℝ)+2)*log (Nat.card K:ℝ) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hc:=projective_card_bound hdim
  have hp : 1≤(Nat.card K:ℝ)^d:=one_le_pow₀ hq
  have hlog : log (3:ℝ)≤2 := by
    have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  calc
    _ ≤ log (3*(Nat.card K:ℝ)^d) := log_le_log (by positivity) (by nlinarith)
    _ = log 3+(d:ℝ)*log (Nat.card K:ℝ) := by
      rw [log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow]
    _ ≤ _ := by nlinarith

variable [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype (Projectivization K V)] [FiniteDimensional K V] in
lemma headerCost_linear {d : ℕ} (hdim : Module.finrank K V=d+3)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    headerCost (K:=K) (V:=V)≤2*((d:ℝ)+4)*log (Nat.card K:ℝ) := by
  have hdual : Module.finrank K (Module.Dual K V)=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdim]
  have hbi : Module.finrank K (Module.Dual K (Module.Dual K V))=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdual]
  have ha:=projective_log_card_add_one hdual hσ
  have hb:=projective_log_card_add_one hbi hσ
  unfold headerCost
  push_cast at ha hb
  linarith

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [FiniteDimensional K V] in
lemma root_potential_linear {d : ℕ} (hdim : Module.finrank K V=d+3)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    potential ((Nat.card K:ℝ)^(d+3))
      ((univ,univ) : ChronoDomains (K:=K) (V:=V))≤2*((d:ℝ)+4)*log (Nat.card K:ℝ) := by
  have hdual : Module.finrank K (Module.Dual K V)=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdim]
  have hdim' : Module.finrank K V=(d+2)+1 := hdim
  have ha:=projective_log_card_add_one hdual hσ
  have hb:=projective_log_card_add_one hdim' hσ
  have hap:=projective_card_positive hdual
  have hbp:=projective_card_positive hdim'
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  unfold potential
  simp only [card_univ]
  apply max_le
  · rw [log_div (mul_ne_zero hap.ne' hbp.ne') (pow_ne_zero _ hq.ne'),
      log_mul hap.ne' hbp.ne',log_pow]
    have ha':=log_le_log hap (show (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)≤
      (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1 by linarith)
    have hb':=log_le_log hbp (show (Fintype.card (Projectivization K V):ℝ)≤
      (Fintype.card (Projectivization K V):ℝ)+1 by linarith)
    push_cast at ha hb ⊢
    nlinarith
  · positivity
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Execution_OutputCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real ExecutedPotential TreeDecoder
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) ]

omit [FiniteDimensional K V] in
lemma reciprocal_cost_envelope {d w h m : ℕ} {b P H σ C : ℝ}
    (hdim : Module.finrank K V=d+3) (hlog : log (Nat.card K:ℝ)=σ)
    (hσ : 1≤σ) (hw : 1≤w) (hh : 1≤h)
    (hH : 0≤H) (hP : 4≤P) (hbP : b+log 1000000≤P)
    (hwlog : log ((w:ℝ)+1)≤C*σ) (hmlog : log ((m:ℝ)+1)≤C*σ) :
    reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H) w h m ≤
      (2*(H+22)*(2*((d:ℝ)+4)+1003))*(Nat.card K:ℝ)*P*(h:ℝ)*(σ+(w:ℝ)*P)+
      (3+2*C+2*((d:ℝ)+4))*(w:ℝ)*σ := by
  have hσ0 : 0≤σ:=by linarith
  have hw1 : (1:ℝ)≤w:=by exact_mod_cast hw
  have hh1 : (1:ℝ)≤h:=by exact_mod_cast hh
  have hP0 : 0≤P:=by linarith
  have hhead:=headerCost_linear hdim (by rwa [hlog])
  have hpot:=root_potential_linear hdim (by rwa [hlog])
  rw [hlog] at hhead hpot
  have hlog2 : log (2:ℝ)≤1 := by
    have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hshape : ((2*w+1:ℕ):ℝ)*log 2≤3*(w:ℝ)*σ := by
    push_cast
    calc
      _ ≤ (2*(w:ℝ)+1)*1 := mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ 3*(w:ℝ) := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hσ
  have hb : b≤P := by linarith [log_nonneg (by norm_num : (1:ℝ)≤1000000)]
  have hab : b+log 4+2*log 2000≤1002*P := by
    have h4:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    have h2:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2000)
    linarith
  have hinner : (h:ℝ)*(potential ((Nat.card K:ℝ)^(d+3))
      ((univ,univ) : ChronoDomains (K:=K) (V:=V))+(w:ℝ)*(b+log 4+2*log 2000))+
      (w:ℝ)*P ≤ (2*((d:ℝ)+4)+1003)*(h:ℝ)*(σ+(w:ℝ)*P) := by
    calc
      _ ≤ (h:ℝ)*(2*((d:ℝ)+4)*σ+(w:ℝ)*(1002*P))+(w:ℝ)*P := by
        gcongr
      _ ≤ (h:ℝ)*(2*((d:ℝ)+4)*σ+(w:ℝ)*(1002*P))+(h:ℝ)*((w:ℝ)*P) := by
        exact add_le_add le_rfl (le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg w) hP0) hh1)
      _ ≤ _ := by
        have h1 : 0≤(h:ℝ)*σ:=by positivity
        have h2 : 0≤(2*((d:ℝ)+4))*(h:ℝ)*((w:ℝ)*P):=by positivity
        nlinarith only [h1,h2]
  unfold reciprocalOutputCost
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have haux : (w:ℝ)*(log ((w:ℝ)+1)+headerCost (K:=K) (V:=V)+log ((m:ℝ)+1))≤
      (w:ℝ)*((2*C+2*((d:ℝ)+4))*σ) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg w)
    linarith
  calc
    _ ≤ 3*(w:ℝ)*σ+(w:ℝ)*((2*C+2*((d:ℝ)+4))*σ)+
        (2*(H+22)*(Nat.card K:ℝ)*P)*((2*((d:ℝ)+4)+1003)*(h:ℝ)*(σ+(w:ℝ)*P)) := by
      exact add_le_add (add_le_add (by simpa only [Nat.cast_add,Nat.cast_one] using hshape) haux)
        (mul_le_mul_of_nonneg_left hinner (by positivity))
    _ = _ := by ring
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Trees_TreeHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ChronologicalTree
open Finset Filter Real BinaryTree
open scoped Classical Topology
noncomputable section

lemma eventually_natLog_small (β C a : ℝ) (hβ : 0<β) (hC : 0<C) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,(n:ℝ)≤C*x^a → (Nat.log 2 n:ℝ)+1≤x^β := by
  have hp : Tendsto (fun x : ℝ=>x^(-β)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hβ
  have hl := (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ=>(log C/log 2+1)*x^(-β)+(a/log 2)*(log x/x^β))
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (hp.const_mul (log C/log 2+1)).add (hl.const_mul (a/log 2))
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop (1:ℝ)] with x hx hx1 n hn
  have hx0 : 0<x := by linarith
  have hp0 : 0<x^β := rpow_pos_of_pos hx0 _
  have hd : 0<log (2:ℝ) := log_pos (by norm_num)
  have hlog : (log C/log 2+1)+(a/log 2)*log x≤x^β := by
    have he : (log C/log 2+1)*x^(-β)+(a/log 2)*(log x/x^β)=
        ((log C/log 2+1)+(a/log 2)*log x)/x^β := by
      rw [rpow_neg hx0.le]
      ring
    rw [he] at hx
    simpa only [one_mul] using ((div_lt_iff₀ hp0).mp hx).le
  rcases eq_or_ne n 0 with rfl|hn0
  · simpa using one_le_rpow hx1 hβ.le
  · have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnlog : log (n:ℝ)≤log C+a*log x := by
      calc
        _ ≤ log (C*x^a) := log_le_log hnpos hn
        _ = _ := by rw [log_mul hC.ne' (rpow_pos_of_pos hx0 a).ne',log_rpow hx0]
    have hnat := Real.natLog_le_logb n 2
    dsimp only [logb] at hnat
    norm_num only [Nat.cast_ofNat] at hnat
    calc
      (Nat.log 2 n:ℝ)+1 ≤ log (n:ℝ)/log 2+1 := by linarith only [hnat]
      _ ≤ (log C+a*log x)/log 2+1 := by gcongr
      _ = (log C/log 2+1)+(a/log 2)*log x := by ring
      _ ≤ _ := hlog

end
end SharpLogRamsey.ChronologicalTree

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_CostContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_monomial_le_power (C a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x^b := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-b)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-b))*x^b := by rw [mul_assoc, ←rpow_add hx0]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hx.le (rpow_nonneg hx0.le _)

lemma P_upper_D {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0 < η)
    (had : Admissible σ η D R) : scaleP σ η D R ≤ 4*D*σ^(9*beta η) := by
  have hb := beta_pos hη
  have hpow : 1 ≤ σ^beta η := one_le_rpow hσ hb.le
  have hD : 0 ≤ D := (rpow_nonneg (by linarith : 0 ≤ σ) _).trans had.D_lower
  have hR : (R:ℝ) ≤ 4*σ^beta η := by linarith [had.R_upper]
  calc
    _ ≤ (D*σ^(8*beta η))*(4*σ^beta η) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = _ := by
      have hp : σ^(8*beta η)*σ^beta η = σ^(9*beta η) := by
        rw [←rpow_add (by linarith : 0 < σ)]
        congr 1
        ring
      linear_combination (4*D)*hp

theorem eventually_literal_cost_contraction (η A B C c : ℝ)
    (hη : 0 < η) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D P h w k : ℝ,
      exp σ = q → 1 ≤ D → 0 ≤ P → P ≤ 4*D*σ^(9*beta η) →
      0 ≤ h → h ≤ σ^beta η → 0 ≤ w → w*D ≤ C*σ^(1+η/2) →
      c*q*σ^(1+η) ≤ k →
      A*q*P*h*(σ+w*P)+B*w*σ ≤ D*σ^(-η/3)*k := by
  have hb := beta_pos hη
  have hgap1 : 1+10*beta η < 1+2*η/3 := by unfold beta; linarith
  have hgap2 : 1+η/2+19*beta η < 1+2*η/3 := by unfold beta; linarith
  have ht := ScaleSelection.eventually_polynomial_exp_neg_rpow_lt
    (B*C) (1-η/6) 1 1 (c/3) (by norm_num) (by norm_num) (by positivity)
  filter_upwards [eventually_monomial_le_power (4*A) (1+10*beta η) (1+2*η/3)
      (c/3) hgap1 (by positivity),
    eventually_monomial_le_power (16*A*C) (1+η/2+19*beta η) (1+2*η/3)
      (c/3) hgap2 (by positivity), ht, eventually_ge_atTop (1:ℝ)]
    with σ h1 h2 h3 hσ q D P h w k hq hD hP hPup hh hhu hw hwD hk
  have hσ0 : 0 < σ := by linarith
  have hq0 : 0 < q := hq ▸ exp_pos _
  have hD0 : 0 < D := by linarith
  have hw' : w ≤ C*σ^(1+η/2) := by nlinarith
  have hf1 : A*q*P*h*σ ≤ (4*A)*σ^(1+10*beta η)*q*D := by
    calc
      _ ≤ A*q*(4*D*σ^(9*beta η))*(σ^beta η)*σ := by gcongr
      _ = _ := by
        have hp : σ^(9*beta η)*σ^beta η*σ = σ^(1+10*beta η) := by
          calc
            _ = σ^(9*beta η+beta η)*σ^(1:ℝ) := by rw [rpow_add hσ0, rpow_one]
            _ = _ := by rw [←rpow_add hσ0]; congr 1; ring
        linear_combination (A*q*4*D)*hp
  have hf2 : A*q*P*h*(w*P) ≤ (16*A*C)*σ^(1+η/2+19*beta η)*q*D := by
    calc
      _ ≤ A*q*(4*D*σ^(9*beta η))*(σ^beta η)*(w*(4*D*σ^(9*beta η))) := by gcongr
      _ = (16*A*q*D)*(w*D)*(σ^(9*beta η)*σ^beta η*σ^(9*beta η)) := by ring
      _ ≤ (16*A*q*D)*(C*σ^(1+η/2))*(σ^(9*beta η)*σ^beta η*σ^(9*beta η)) := by gcongr
      _ = _ := by
        have hp : σ^(1+η/2)*(σ^(9*beta η)*σ^beta η*σ^(9*beta η)) =
            σ^(1+η/2+19*beta η) := by
          rw [←rpow_add hσ0, ←rpow_add hσ0, ←rpow_add hσ0]
          congr 1
          ring
        linear_combination (16*A*q*D*C)*hp
  have hf3 : B*w*σ ≤ (c/3)*σ^(1+2*η/3)*q*D := by
    have he3 : B*C*σ^(1-η/6)*exp (-σ) ≤ c/3 := by
      simpa only [rpow_one, one_mul, neg_one_mul] using h3.le
    have h31 : B*C*σ^(1-η/6) ≤ (c/3)*q := by
      have hh := mul_le_mul_of_nonneg_right he3 (exp_nonneg σ)
      rw [mul_assoc (B*C*σ^(1-η/6)), ←exp_add, neg_add_cancel, exp_zero, mul_one] at hh
      simpa only [hq] using hh
    have h32 := mul_le_mul_of_nonneg_right h31 (rpow_nonneg hσ0.le (1+2*η/3))
    have he : σ^(1-η/6)*σ^(1+2*η/3) = σ^(2+η/2) := by
      rw [←rpow_add hσ0]
      congr 1
      ring
    rw [mul_assoc (B*C), he] at h32
    calc
      _ ≤ B*(C*σ^(1+η/2))*σ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw' hB) le_rfl hσ0.le
          (mul_nonneg hB (mul_nonneg hC (rpow_nonneg hσ0.le _)))
      _ = B*C*σ^(2+η/2) := by
        have hp : σ^(1+η/2)*σ = σ^(2+η/2) := by
          calc
            _ = σ^(1+η/2)*σ^(1:ℝ) := by rw [rpow_one]
            _ = _ := by rw [←rpow_add hσ0]; congr 1; ring
        linear_combination (B*C)*hp
      _ ≤ (c/3)*q*σ^(1+2*η/3) := h32
      _ ≤ (c/3)*σ^(1+2*η/3)*q*D := by
        nlinarith [mul_le_mul_of_nonneg_left hD
          (by positivity : 0 ≤ (c/3)*q*σ^(1+2*η/3))]
  have h1' := mul_le_mul_of_nonneg_right h1 (mul_nonneg hq0.le hD0.le)
  have h2' := mul_le_mul_of_nonneg_right h2 (mul_nonneg hq0.le hD0.le)
  have hk' := mul_le_mul_of_nonneg_left hk (mul_nonneg hD0.le (rpow_nonneg hσ0.le (-η/3)))
  have he : D*σ^(-η/3)*(c*q*σ^(1+η)) = c*σ^(1+2*η/3)*q*D := by
    have hp : σ^(-η/3)*σ^(1+η)=σ^(1+2*η/3) := by
      rw [←rpow_add hσ0]
      congr 1
      ring
    linear_combination (D*c*q)*hp
  rw [he] at hk'
  nlinarith only [hf1,hf2,hf3,h1',h2',hk']
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_LogWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_log_window (C a : ℝ) (hC : 0<C) (ha : 0≤a) :
    ∀ᶠ σ : ℝ in atTop, ∀ x : ℝ, 0≤x → x≤C*exp σ*σ^a →
      log (x+1)≤(a+2)*σ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (log (C+1))]
    with σ hσ hCσ x hx hxup
  have hσ0 : 0<σ:=by linarith
  have he : 1≤exp σ:=one_le_exp hσ0.le
  have hp : 1≤σ^a:=one_le_rpow hσ ha
  have hup : x+1≤(C+1)*exp σ*σ^a := by
    have hh : 1≤exp σ*σ^a:=one_le_mul_of_one_le_of_one_le he hp
    nlinarith only [hxup,hh]
  have hl:=log_le_log (by linarith : 0<x+1) hup
  rw [log_mul (mul_ne_zero (by linarith : C+1≠0) (exp_ne_zero _))
    (rpow_pos_of_pos hσ0 a).ne',log_mul (by linarith : C+1≠0) (exp_ne_zero _),
    log_exp,log_rpow hσ0] at hl
  have hs : log σ≤σ:= (log_le_sub_one_of_pos hσ0).trans (by linarith)
  have hhs:=mul_le_mul_of_nonneg_left hs ha
  nlinarith only [hl,hCσ,hhs]
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Marking_StepCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter SourceScales
open scoped Classical Topology
noncomputable section

theorem eventually_reciprocal_message_cost_oai (i : ℕ) (η c C H : ℝ)
    (hη : 0 < η) (hc : 0 < c) (hC : 0 < C) (hH : 0 ≤ H) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
      [Fintype (Projectivization (ZMod q) V)]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) V))]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Module.Dual (ZMod q) V)))],
      Module.finrank (ZMod q) V=i+4 →
    ∀ (D : ℝ) (R w n k m : ℕ), Admissible σ η D R →
      1 ≤ w → c*(q:ℝ)*σ^(1+η) ≤ m →
      (w:ℝ)*D ≤ C*σ^(1+η/2) → (w:ℝ) ≤ C*σ^(1+η/2) →
      (4*(n+k):ℕ) ≤ C*(q:ℝ)*σ^(1+η/2) →
      4 ≤ scaleP σ η D R → 16*scaleKstar σ η D+log 1000000 ≤ scaleP σ η D R →
    reciprocalOutputCost (K:=ZMod q) (V:=V) (I:=Fin w)
      (d:=i+1) (b:=16*scaleKstar σ η D) (P:=scaleP σ η D R) (H:=H)
      w (Nat.log 2 w+1) (2*(n+k)) ≤ D*σ^(-η/3)*m := by
  let a:=1+η/2
  let Cl:=a+2
  let A:=2*(H+22)*(2*(((i+1:ℕ):ℝ)+4)+1003)
  let B:=3+2*Cl+2*(((i+1:ℕ):ℝ)+4)
  have ha : 0 ≤ a:=by dsimp only [a];linarith
  have hA : 0 ≤ A:=by dsimp only [A];positivity
  have hB : 0 ≤ B:=by dsimp only [B,Cl,a];positivity
  filter_upwards [eventually_literal_cost_contraction η A B C c hη hA hB hC.le hc,
    ChronologicalTree.eventually_natLog_small (beta η) C a (beta_pos hη) hC,
    eventually_log_window C a hC ha,eventually_ge_atTop (1:ℝ)]
      with σ hcost hheight hlogwin hσ
  intro q _ he V _ _ _ _ _ _ hdim D R w n k m had hw hmlo hwD hwup hLup hP hbP
  have hσ0 : 0 < σ:=by linarith
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  have hqlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  have hwlog : log ((w:ℝ)+1) ≤ Cl*σ:=by
    apply hlogwin _ (Nat.cast_nonneg _)
    have he1 : 1 ≤ exp σ:=one_le_exp hσ0.le
    calc
      _ ≤ C*σ^a:=hwup
      _ ≤ C*exp σ*σ^a:=by nlinarith [mul_le_mul_of_nonneg_right he1 (by positivity : 0 ≤ C*σ^a)]
  have hmlog : log ((2*(n+k):ℕ)+1:ℝ) ≤ Cl*σ:=by
    apply hlogwin _ (Nat.cast_nonneg _)
    calc
      _ ≤ ((4*(n+k):ℕ):ℝ):=by push_cast;linarith [show (0:ℝ) ≤ n by positivity,show (0:ℝ) ≤ k by positivity]
      _ ≤ C*(q:ℝ)*σ^a:=hLup
      _ = C*exp σ*σ^a:=by rw [he]
  apply (reciprocal_cost_envelope hdim hqlog hσ hw
    (show 1 ≤ Nat.log 2 w+1 by omega) hH hP hbP hwlog hmlog (m:=2*(n+k))).trans
  simpa only [A,B,Nat.card_zmod,Nat.cast_add,Nat.cast_one] using
    hcost (q:ℝ) D (scaleP σ η D R) (Nat.log 2 w+1:ℝ) (w:ℝ) (m:ℝ)
      he hD (by linarith) (P_upper_D hσ hη had) (by positivity)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hheight w hwup)
      (Nat.cast_nonneg _) hwD hmlo
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost_oai := @OAI.SharpLogRamsey.ActualPivot.eventually_reciprocal_message_cost_oai

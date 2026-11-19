-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_running_time
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:11:06.238525+00:00
-- url     : https://prove2.me/submissions/3d9a7e74-8090-4ac8-a002-463edc3e4c1b

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
lemma region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RegionInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).1

theorem root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootIdentity g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.1

lemma layer_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    LayerIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.1

lemma root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).q = q := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

lemma depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).top ≤ ℓ := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).1

lemma budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.1

lemma cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CacheControlInvariant ℓ (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.1

lemma parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ParameterInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

lemma keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    KeysInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

lemma isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    IsolateResidual g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

lemma stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

lemma numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

end
end NearlyOptimalPPR.Computation


-- Proof module: Solutions.BalancedBlocks

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma blockSearch_exact (N : ℝ) (r K fuel candidate : ℕ)
    (hcond : ∀ k : ℕ, (k : ℝ)^(r+2) ≤ N^(r+1) ↔ k ≤ K)
    (hc : candidate ≤ K) (hf : K < candidate+fuel) :
    blockSearch N r fuel candidate = K := by
  induction fuel generalizing candidate with
  | zero => omega
  | succ fuel ih =>
    unfold blockSearch
    by_cases he : candidate+1 ≤ K
    · rw [if_pos ((hcond _).mpr he)]
      exact ih (candidate+1) he (by omega)
    · rw [if_neg (fun h => he ((hcond _).mp h))]
      omega

lemma block_power_condition (N : ℝ) (hN : 1 ≤ N) (r k : ℕ) :
    (k : ℝ)^(r+2) ≤ N^(r+1) ↔
      (k : ℝ) ≤ N^((r+1 : ℝ)/(r+2)) := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hden : (r+2 : ℝ) ≠ 0 := by positivity
  have hp : (N^((r+1 : ℝ)/(r+2)))^(r+2 : ℕ) = N^(r+1) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0]
    have he : ((r+1 : ℝ)/(r+2))*((r+2 : ℕ) : ℝ) = (r+1 : ℕ) := by
      push_cast
      field_simp
    rw [he,Real.rpow_natCast]
  rw [←hp]
  exact pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hN0 _) (by omega)

lemma balanced_block_exact (N : ℝ) (hN : 1 ≤ N) (r : ℕ) :
    blockSearch N r (⌈N⌉₊+1) 0 = ⌊N^((r+1 : ℝ)/(r+2))⌋₊ := by
  let x := N^((r+1 : ℝ)/(r+2))
  have hx0 : 0 ≤ x := Real.rpow_nonneg (le_trans zero_le_one hN) _
  have hxN : x ≤ N := Real.rpow_le_self_of_one_le hN ((div_le_one (by positivity)).mpr (by linarith))
  apply blockSearch_exact N r ⌊x⌋₊ _ 0
  · intro k
    rw [block_power_condition N hN r k]
    exact (Nat.le_floor_iff hx0).symm
  · exact Nat.zero_le _
  · have hf : (⌊x⌋₊ : ℝ) ≤ N := (Nat.floor_le hx0).trans hxN
    have hc : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
    have : ⌊x⌋₊ ≤ ⌈N⌉₊ := by exact_mod_cast hf.trans hc
    omega

lemma blockScale_balanced (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    blockScale [] ℓ j N = ⌊N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))⌋₊ := by
  unfold blockScale
  simp only [List.getElem?_nil]
  rw [balanced_block_exact N hN]
  have hx : 1 ≤ N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2)) :=
    Real.one_le_rpow hN (by positivity)
  have hf : 1 ≤ ⌊N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))⌋₊ := by
    exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hx)
  exact max_eq_right hf

lemma floor_half_bounds (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ x/2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hf := Nat.lt_floor_add_one x
  refine ⟨h1,?_,Nat.floor_le hx0⟩
  by_cases hh : 2 ≤ x
  · linarith
  · have hc : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    linarith

lemma balanced_block_bounds (ℓ j : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    let x := N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2))
    let b := blockScale [] ℓ j N
    1 ≤ b ∧ x/2 ≤ (b : ℝ) ∧ (b : ℝ) ≤ x ∧ (b : ℝ) ≤ N := by
  rw [blockScale_balanced ℓ j N hN]
  have hx : 1 ≤ N^(((ℓ-j : ℕ)+1 : ℝ)/((ℓ-j : ℕ)+2)) := Real.one_le_rpow hN (by positivity)
  obtain ⟨h1,h2,h3⟩ := floor_half_bounds _ hx
  exact ⟨h1,h2,h3,h3.trans (Real.rpow_le_self_of_one_le hN ((div_le_one (by positivity)).mpr (by linarith)))⟩

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RecurrenceAlgebra

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma balance_product (N : ℝ) (hN : 1 ≤ N) (r : ℕ) :
    N^(1+1/(r+2 : ℝ))*N^((r+1 : ℝ)/(r+2)) = N^2 := by
  rw [←Real.rpow_add (lt_of_lt_of_le zero_lt_one hN)]
  have he : (1+1/(r+2 : ℝ))+(r+1 : ℝ)/(r+2) = 2 := by field_simp; ring
  rw [he,Real.rpow_two]

lemma balance_first_term (N b : ℝ) (hN : 1 ≤ N) (hb : 0 < b) (r : ℕ)
    (hx : N^((r+1 : ℝ)/(r+2))/2 ≤ b) :
    N^2/b ≤ 2*N^(1+1/(r+2 : ℝ)) := by
  apply (div_le_iff₀ hb).mpr
  have hE : 0 ≤ N^(1+1/(r+2 : ℝ)) := Real.rpow_nonneg (le_trans zero_le_one hN) _
  calc
    _ = N^(1+1/(r+2 : ℝ))*N^((r+1 : ℝ)/(r+2)) := (balance_product N hN r).symm
    _ ≤ N^(1+1/(r+2 : ℝ))*(2*b) := mul_le_mul_of_nonneg_left (by linarith) hE
    _ = _ := by ring

lemma balance_second_term (N b : ℝ) (hN : 1 ≤ N) (hb : 0 < b) (r : ℕ)
    (hx : b ≤ N^((r+1 : ℝ)/(r+2))) :
    N/b*b^(1+1/(r+1 : ℝ)) ≤ N^(1+1/(r+2 : ℝ)) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbpow : b^(1+1/(r+1 : ℝ)) = b*b^(1/(r+1 : ℝ)) := by rw [Real.rpow_add hb,Real.rpow_one]
  rw [hbpow]
  have hcancel : N/b*(b*b^(1/(r+1 : ℝ))) = N*b^(1/(r+1 : ℝ)) := by field_simp
  rw [hcancel]
  calc
    _ ≤ N*(N^((r+1 : ℝ)/(r+2)))^(1/(r+1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb.le hx (by positivity)) hN0.le
    _ = _ := by
      rw [←Real.rpow_mul hN0.le]
      nth_rw 1 [←Real.rpow_one N]
      rw [←Real.rpow_add hN0]
      congr 1
      field_simp

lemma balance_leaf_second (N b : ℝ) (hN : 1 ≤ N) (hx : b ≤ N^((1 : ℝ)/2)) :
    N*b ≤ N^(1+(1 : ℝ)/2) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ N*N^((1 : ℝ)/2) := mul_le_mul_of_nonneg_left hx hN0.le
    _ = _ := by
      nth_rw 1 [←Real.rpow_one N]
      rw [←Real.rpow_add hN0]

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedRecurrence

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation

lemma balanced_recurrence (R : ℕ → ℝ → ℝ≥0∞) (ℓ : ℕ) (P : ℝ) (hP : 1 ≤ P)
    (hleaf : ∀ N : ℝ, 1 ≤ N →
      let b : ℝ := blockScale [] ℓ ℓ N
      R ℓ N ≤ ENNReal.ofReal (P*(N^2/b+N*b)))
    (hstep : ∀ (j : ℕ) (N : ℝ), j < ℓ → 1 ≤ N →
      let b : ℝ := blockScale [] ℓ j N
      R j N ≤ ENNReal.ofReal P*(ENNReal.ofReal (N^2/b)+
        ENNReal.ofReal (N/b)*R (j+1) b)+ENNReal.ofReal (P*N)) :
    ∀ (r j : ℕ), j+r=ℓ → ∀ N : ℝ, 1 ≤ N →
      R j N ≤ ENNReal.ofReal ((4*P)^(r+1)*N^(1+1/(r+2 : ℝ))) := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  intro r
  induction r with
  | zero =>
    intro j hj N hN
    have hjj : j = ℓ := by omega
    subst j
    let b : ℝ := blockScale [] ℓ ℓ N
    have hb := balanced_block_bounds ℓ ℓ N hN
    simp only [Nat.sub_self,Nat.cast_zero,zero_add] at hb
    have hb1 : 1 ≤ b := by
      dsimp only [b]
      exact_mod_cast hb.1
    have hfirst := balance_first_term N b hN (lt_of_lt_of_le zero_lt_one hb1) 0 (by simpa using hb.2.1)
    have hsecond := balance_leaf_second N b hN (by simpa using hb.2.2.1)
    have hE : 0 ≤ N^(1+(1 : ℝ)/2) := Real.rpow_nonneg (le_trans zero_le_one hN) _
    calc
      R ℓ N ≤ ENNReal.ofReal (P*(N^2/b+N*b)) := hleaf N hN
      _ ≤ ENNReal.ofReal (4*P*N^(1+(1 : ℝ)/2)) := ENNReal.ofReal_le_ofReal (by
        have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hP0
        norm_num at hh ⊢
        nlinarith [mul_nonneg hP0 hE])
      _ = _ := by norm_num
  | succ r ih =>
    intro j hj N hN
    have hjl : j < ℓ := by omega
    have hsub : ℓ-j = r+1 := by omega
    let b : ℝ := blockScale [] ℓ j N
    have hb := balanced_block_bounds ℓ j N hN
    rw [hsub] at hb
    have hb1 : 1 ≤ b := by
      dsimp only [b]
      exact_mod_cast hb.1
    have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb1
    have hNr : 0 ≤ N := le_trans zero_le_one hN
    let A := (4*P)^(r+1)
    let E := N^(1+1/((r+1 : ℕ)+2 : ℝ))
    have hA : 1 ≤ A := by
      dsimp only [A]
      exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 4*P)
    have hE : 0 ≤ E := Real.rpow_nonneg hNr _
    have hfirst := balance_first_term N b hN hb0 (r+1) hb.2.1
    have hsecond := balance_second_term N b hN hb0 (r+1) hb.2.2.1
    have hNle : N ≤ E := by
      have hexp : (1 : ℝ) ≤ 1+1/((r+1 : ℕ)+2 : ℝ) := by
        have hpos : (0 : ℝ) ≤ 1/((r+1 : ℕ)+2 : ℝ) := by positivity
        linarith
      have hh := Real.rpow_le_rpow_of_exponent_le hN hexp
      simpa [E] using hh
    have hchild := ih (j+1) (by omega) b hb1
    have heq : ENNReal.ofReal P*(ENNReal.ofReal (N^2/b)+
        ENNReal.ofReal (N/b)*ENNReal.ofReal (A*b^(1+1/(r+2 : ℝ))))+ENNReal.ofReal (P*N) =
        ENNReal.ofReal (P*(N^2/b+N/b*(A*b^(1+1/(r+2 : ℝ))))+P*N) := by
      rw [←ENNReal.ofReal_mul (div_nonneg hNr hb0.le),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul hP0,←ENNReal.ofReal_add (by positivity) (by positivity)]
    calc
      R j N ≤ ENNReal.ofReal P*(ENNReal.ofReal (N^2/b)+ENNReal.ofReal (N/b)*R (j+1) b)+
          ENNReal.ofReal (P*N) := hstep j N hjl hN
      _ ≤ ENNReal.ofReal P*(ENNReal.ofReal (N^2/b)+
          ENNReal.ofReal (N/b)*ENNReal.ofReal (A*b^(1+1/(r+2 : ℝ))))+ENNReal.ofReal (P*N) := by
        gcongr
      _ = ENNReal.ofReal (P*(N^2/b+N/b*(A*b^(1+1/(r+2 : ℝ))))+P*N) := heq
      _ ≤ ENNReal.ofReal ((4*P)^(r+1+1)*E) := ENNReal.ofReal_le_ofReal (by
        have hsec : N/b*(A*b^(1+1/(r+2 : ℝ))) ≤ A*E := by
          have hs : N/b*b^(1+1/(r+2 : ℝ)) ≤ E := by
            simpa only [E,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hsecond
          calc
            _ = A*(N/b*b^(1+1/(r+2 : ℝ))) := by ring
            _ ≤ A*E := mul_le_mul_of_nonneg_left hs (le_trans zero_le_one hA)
        have hh := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hfirst hsec) hP0)
          (mul_le_mul_of_nonneg_left hNle hP0)
        change _ ≤ P*(2*E+A*E)+P*E at hh
        rw [pow_succ]
        change _ ≤ A*(4*P)*E
        apply hh.trans
        calc
          P*(2*E+A*E)+P*E = (A+3)*(P*E) := by ring
          _ ≤ (4*A)*(P*E) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hP0 hE)
          _ = _ := by ring)
      _ = _ := by rfl

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedDepthScalars

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mpr
  exact Real.exp_one_lt_three.trans (by norm_num)

lemma balanced_depth_scalar_bounds (t : ℝ) (ht : 0 ≤ t) :
    let L := Real.log 2+t
    let S := Real.log 4+t
    let H := Real.log S
    let d := Real.sqrt (L/H)
    let R := Real.sqrt (L*H)
    let B := 4+1/Real.log (Real.log 4)
    0 < H ∧ H ≤ L ∧ 0 < d ∧ d*H=R ∧ H ≤ R ∧
      1 ≤ B ∧ d+3 ≤ B*S ∧ 2+L+d ≤ B*S := by
  intro L S H d R B
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl2one : Real.log (2 : ℝ) ≤ 1 := by simpa only [show (2 : ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hl4 : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hS : 1 < S := by dsimp only [S]; linarith [log_four_gt_one]
  have hS0 : 0 < S := by linarith
  have hL : 0 < L := by dsimp only [L]; linarith
  have hH : 0 < H := Real.log_pos hS
  have hHle : H ≤ L := by
    have hh := Real.log_le_sub_one_of_pos hS0
    dsimp only [H,S,L] at hh ⊢
    linarith
  have hh0 : 0 < Real.log (Real.log (4 : ℝ)) := Real.log_pos log_four_gt_one
  have hhH : Real.log (Real.log (4 : ℝ)) ≤ H := Real.log_le_log
    (by linarith [log_four_gt_one]) (by dsimp only [S]; linarith)
  have hd : 0 < d := Real.sqrt_pos.mpr (div_pos hL hH)
  have hd2 : d^2=L/H := Real.sq_sqrt (div_nonneg hL.le hH.le)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2=L*H := Real.sq_sqrt (mul_nonneg hL.le hH.le)
  have hdH : d*H=R := by
    have he : (d*H)^2=R^2 := by
      rw [mul_pow,hd2,hR2]
      field_simp
    nlinarith [mul_pos hd hH]
  have hHR : H ≤ R := by nlinarith
  have hB : 1 ≤ B := by
    have hh : 0 < 1/Real.log (Real.log (4 : ℝ)) := by positivity
    dsimp only [B]
    linarith
  have hLleS : L ≤ S := by dsimp only [L,S]; linarith
  have hfrac : L/H ≤ S/Real.log (Real.log 4) := by gcongr
  have hdBound : d ≤ (1+1/Real.log (Real.log 4))*S := by
    have hh := sq_nonneg (d-1/2)
    have heq : S/Real.log (Real.log 4)+1 ≤ (1+1/Real.log (Real.log 4))*S := by
      have hs1 : 1 ≤ S := hS.le
      field_simp
      nlinarith
    nlinarith
  refine ⟨hH,hHle,hd,hdH,hHR,hB,?_,?_⟩
  all_goals dsimp only [B]; nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedDepthLogs

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma absorb_log_constant (H h a : ℝ) (hh : 0 < h) (hH : h ≤ H) (ha : 0 ≤ a) :
    a+H ≤ (1+a/h)*H := by
  have hm := mul_le_mul_of_nonneg_left hH (div_nonneg ha hh.le)
  have he : a/h*h=a := div_mul_cancel₀ a hh.ne'
  nlinarith

lemma balanced_depth_log_bounds (t : ℝ) (ht : 0 ≤ t) :
    let L := Real.log 2+t
    let S := Real.log 4+t
    let H := Real.log S
    let d := Real.sqrt (L/H)
    let R := Real.sqrt (L*H)
    let ℓ := ⌊d⌋₊
    let h := Real.log (Real.log 4)
    let B := 4+1/h
    let A := 1+Real.log B/h
    let K := 1+(Real.log 32+Real.log B)/h
    0 < H ∧ H ≤ L ∧ H ≤ R ∧
      0 < d ∧ (ℓ : ℝ) ≤ d ∧ d ≤ (ℓ : ℝ)+1 ∧
      1 ≤ A ∧ 1 ≤ K ∧
      Real.log ((ℓ : ℝ)+3) ≤ A*H ∧
      Real.log (2+L+(ℓ : ℝ)) ≤ A*H ∧
      Real.log (32*((ℓ : ℝ)+3)) ≤ K*H ∧
      L ≤ ((ℓ : ℝ)+2)*R ∧ ((ℓ : ℝ)+1)*H ≤ 2*R := by
  intro L S H d R ℓ h B A K
  obtain ⟨hH,hHL,hd,hdH,hHR,hB,hdB,hXB⟩ := balanced_depth_scalar_bounds t ht
  change 0 < H at hH
  change H ≤ L at hHL
  change 0 < d at hd
  change d*H=R at hdH
  change H ≤ R at hHR
  have hh : 0 < h := Real.log_pos log_four_gt_one
  have hS : 0 < S := by dsimp only [S]; linarith [log_four_gt_one]
  have hL : 0 < L := by dsimp only [L]; linarith [Real.log_pos (by norm_num : (1 : ℝ)<2)]
  have hhH : h ≤ H := Real.log_le_log (by linarith [log_four_gt_one])
    (by dsimp only [S]; linarith)
  have hBpos : 0 < B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hflo : (ℓ : ℝ) ≤ d := Nat.floor_le hd.le
  have hceil : d ≤ (ℓ : ℝ)+1 := (Nat.lt_floor_add_one d).le
  have hκ : 0 < (ℓ : ℝ)+3 := by positivity
  have hX : 0 < 2+L+(ℓ : ℝ) := by positivity
  have hκB : (ℓ : ℝ)+3 ≤ B*S := by linarith
  have hXB' : 2+L+(ℓ : ℝ) ≤ B*S := by linarith
  have hlogκ : Real.log ((ℓ : ℝ)+3) ≤ Real.log B+H := by
    have hh' := Real.log_le_log hκ hκB
    rwa [Real.log_mul hBpos.ne' hS.ne'] at hh'
  have hlogX : Real.log (2+L+(ℓ : ℝ)) ≤ Real.log B+H := by
    have hh' := Real.log_le_log hX hXB'
    rwa [Real.log_mul hBpos.ne' hS.ne'] at hh'
  have hA : 1 ≤ A := by dsimp only [A]; exact le_add_of_nonneg_right (div_nonneg hlogB hh.le)
  have hK : 1 ≤ K := by dsimp only [K]; exact le_add_of_nonneg_right (div_nonneg (add_nonneg hlog32 hlogB) hh.le)
  have hAbsorb := absorb_log_constant H h (Real.log B) hh hhH hlogB
  have hAbsorbK := absorb_log_constant H h (Real.log 32+Real.log B) hh hhH (add_nonneg hlog32 hlogB)
  have hd2 : d^2=L/H := Real.sq_sqrt (div_nonneg hL.le hH.le)
  have hrel : L=d*R := by
    rw [←hdH]
    have he : d^2*H=L := ((div_eq_iff hH.ne').mp hd2.symm).symm
    nlinarith
  refine ⟨hH,hHL,hHR,hd,hflo,hceil,hA,hK,hlogκ.trans hAbsorb,hlogX.trans hAbsorb,?_,?_,?_⟩
  · rw [Real.log_mul (by norm_num : (32 : ℝ)≠0) hκ.ne']
    linarith
  · rw [hrel]
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    nlinarith
  · nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedScalarWork

set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearlyOptimalPPR.Computation

set_option maxHeartbeats 2000000 in
lemma balanced_scalar_work_bound (C : ℝ) (p : ℕ) (hC : 1 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      let L := Real.log 2+t
      let H := Real.log (Real.log 4+t)
      let ℓ := ⌊Real.sqrt (L/H)⌋₊
      let P := C*(2+L+(ℓ : ℝ))^p
      let N := 32*((ℓ : ℝ)+3)*Real.exp t
      (4*P)^(ℓ+1)*N^(1+1/((ℓ : ℝ)+2)) ≤
        Real.exp (t+c*Real.sqrt (L*H)) := by
  let h := Real.log (Real.log (4 : ℝ))
  let B := 4+1/h
  let A := 1+Real.log B/h
  let K := 1+(Real.log 32+Real.log B)/h
  let AP := (p : ℝ)*A+(Real.log 4+Real.log C)/h
  let c := 2*AP+1+2*K
  have hh : 0 < h := Real.log_pos log_four_gt_one
  have hB : 1 ≤ B := by
    have hinv : 0 ≤ 1/h := by positivity
    dsimp only [B]
    linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := log_four_gt_one.le.trans' (by norm_num)
  have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hA : 1 ≤ A := by dsimp only [A]; exact le_add_of_nonneg_right (div_nonneg hlogB hh.le)
  have hK : 1 ≤ K := by dsimp only [K]; exact le_add_of_nonneg_right (div_nonneg (add_nonneg hlog32 hlogB) hh.le)
  have hAP : 0 ≤ AP := by dsimp only [AP]; positivity
  refine ⟨c,by dsimp only [c]; linarith,?_⟩
  intro t ht L H ℓ P N
  let R := Real.sqrt (L*H)
  obtain ⟨hH,hHL,hHR,hd,hflo,hceil,hA',hK',hlκ,hlX,hl32κ,hLR,hElH⟩ := balanced_depth_log_bounds t ht
  change 0 < H at hH
  change H ≤ L at hHL
  change H ≤ R at hHR
  change Real.log ((ℓ : ℝ)+3) ≤ A*H at hlκ
  change Real.log (2+L+(ℓ : ℝ)) ≤ A*H at hlX
  change Real.log (32*((ℓ : ℝ)+3)) ≤ K*H at hl32κ
  change L ≤ ((ℓ : ℝ)+2)*R at hLR
  change ((ℓ : ℝ)+1)*H ≤ 2*R at hElH
  have hL : 0 < L := by dsimp only [L]; linarith [Real.log_pos (by norm_num : (1 : ℝ)<2)]
  have hX : 0 < 2+L+(ℓ : ℝ) := by positivity
  have hN : 0 < N := by dsimp only [N]; positivity
  have hP : 0 < P := by dsimp only [P]; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hhH : h ≤ H := Real.log_le_log (by linarith [log_four_gt_one])
    (by linarith)
  have hl4P : Real.log (4*P) ≤ AP*H := by
    have hmult := mul_le_mul_of_nonneg_left hlX (Nat.cast_nonneg p)
    have ha := absorb_log_constant H h (Real.log 4+Real.log C) hh hhH (add_nonneg hlog4 hlogC)
    have hconst : Real.log 4+Real.log C ≤ ((Real.log 4+Real.log C)/h)*H := by linarith
    rw [Real.log_mul (by norm_num : (4 : ℝ)≠0) hP.ne']
    dsimp only [P]
    rw [Real.log_mul (by linarith : C≠0) (pow_ne_zero _ hX.ne'),Real.log_pow]
    dsimp only [AP]
    nlinarith
  have hlN : Real.log N=t+Real.log (32*((ℓ : ℝ)+3)) := by
    dsimp only [N]
    rw [Real.log_mul (by positivity : 32*((ℓ : ℝ)+3)≠0) (Real.exp_ne_zero t),Real.log_exp]
    ring
  have htL : t ≤ L := by dsimp only [L]; linarith [Real.log_pos (by norm_num : (1 : ℝ)<2)]
  have hlNL : Real.log N ≤ (1+K)*L := by
    have hkHL := mul_le_mul_of_nonneg_left hHL (by linarith : 0 ≤ K)
    rw [hlN]
    nlinarith
  have hM : 0 < (ℓ : ℝ)+2 := by positivity
  have hfrac : Real.log N/((ℓ : ℝ)+2) ≤ (1+K)*R := by
    apply (div_le_iff₀ hM).mpr
    have hm := mul_le_mul_of_nonneg_left hLR (by linarith : 0 ≤ 1+K)
    nlinarith
  have hpterm : ((ℓ : ℝ)+1)*Real.log (4*P) ≤ 2*AP*R := by
    have hm := mul_le_mul_of_nonneg_left hl4P (by positivity : 0 ≤ (ℓ : ℝ)+1)
    have hn := mul_le_mul_of_nonneg_left hElH hAP
    calc
      _ ≤ ((ℓ : ℝ)+1)*(AP*H) := hm
      _ = AP*(((ℓ : ℝ)+1)*H) := by ring
      _ ≤ AP*(2*R) := hn
      _ = _ := by ring
  apply (Real.log_le_log_iff (mul_pos (pow_pos (by positivity : 0 < 4*P) _) (Real.rpow_pos_of_pos hN _))
    (Real.exp_pos _)).mp
  rw [Real.log_mul (pow_ne_zero _ (by positivity : 4*P≠0)) (Real.rpow_pos_of_pos hN _).ne',
    Real.log_pow,Real.log_rpow hN,Real.log_exp]
  push_cast
  have hKN := mul_le_mul_of_nonneg_left hHR (by linarith : 0 ≤ K)
  have hpart : (1+1/((ℓ : ℝ)+2))*Real.log N=Real.log N+Real.log N/((ℓ : ℝ)+2) := by ring
  have hlogNbound : Real.log N ≤ t+K*R := by rw [hlN]; linarith
  rw [hpart]
  change ((ℓ : ℝ)+1)*Real.log (4*P)+(Real.log N+Real.log N/((ℓ : ℝ)+2)) ≤ t+c*R
  dsimp only [c]
  nlinarith

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.BalancedEnvelope

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma balanced_recurrence_envelope (C : ℝ) (p : ℕ) (hC : 1 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      let ℓ := balancedDepth ε
      let P := overhead C p ε ℓ
      let N := 1/rootThreshold ε ℓ
      (4*P)^(ℓ+1)*N^(1+1/((ℓ : ℝ)+2)) ≤ envelope 1 c ε := by
  obtain ⟨c,hc,hBound⟩ := balanced_scalar_work_bound C p hC
  refine ⟨c,hc,?_⟩
  intro ε he he1 ℓ P N
  let t := -Real.log ε
  let L := Real.log 2+t
  let H := Real.log (Real.log 4+t)
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos he.le he1)
  have h2 : Real.log (2/ε)=L := by
    rw [Real.log_div (by norm_num : (2 : ℝ)≠0) he.ne']
    dsimp only [L,t]
    ring
  have h4 : Real.log (4/ε)=Real.log 4+t := by
    rw [Real.log_div (by norm_num : (4 : ℝ)≠0) he.ne']
    dsimp only [t]
    ring
  have hell : ℓ=⌊Real.sqrt (L/H)⌋₊ := by
    dsimp only [ℓ,balancedDepth]
    rw [h2,h4]
  have hExp : Real.exp t=1/ε := by
    dsimp only [t]
    rw [Real.exp_neg,Real.exp_log he]
    simp only [one_div]
  have hP : P=C*(2+L+(ℓ : ℝ))^p := by
    dsimp only [P,overhead]
    rw [h2]
  have hN : N=32*((ℓ : ℝ)+3)*Real.exp t := by
    dsimp only [N,rootThreshold,kappa]
    rw [hExp]
    simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_ofNat]
    field_simp
  have hs := hBound t ht
  dsimp only at hs
  calc
    _ = (4*(C*(2+L+(ℓ : ℝ))^p))^(ℓ+1)*(32*((ℓ : ℝ)+3)*Real.exp t)^(1+1/((ℓ : ℝ)+2)) := by rw [hP,hN]
    _ ≤ Real.exp (t+c*Real.sqrt (L*H)) := by simpa only [hell] using hs
    _ = envelope 1 c ε := by
      unfold envelope
      rw [h2,h4,Real.exp_add,hExp]
      ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.QueueExterior

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma observe_changeFrame {β : Type*} (F : NormalizeFrame n → β) (st : RecursiveState n)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n)
    (hf : F (f (st.frames j)) = F (st.frames j)) (i : ℕ) :
    F ((changeFrame st j f).frames i) = F (st.frames i) := by
  by_cases he : i = j
  · subst i
    simpa [changeFrame] using hf
  · simp [changeFrame,he]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.FrameParameters

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
lemma exterior_parameters (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    frameParameters ((exteriorPush g α st t v).frames i) = frameParameters (st.frames i) := by
  classical
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let δ := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base := rawExterior g α st t v δ
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges+
    (g.neighbors v).length-2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  let prepared := if relative st t v+δ = 3*f.q/8 then final else base
  have hprepared (i : ℕ) : frameParameters (prepared.frames i) = frameParameters (st.frames i) := by
    have hb (i : ℕ) : frameParameters (base.frames i) = frameParameters (st.frames i) := by
      by_cases hh : i ≤ st.top <;> simp [base,rawExterior,hh,frameParameters]
    have ha (i : ℕ) : frameParameters (admitted.frames i) = frameParameters (st.frames i) := by
      exact (observe_changeFrame frameParameters base t _ rfl i).trans (hb i)
    have hc (i : ℕ) : frameParameters (child.frames i) = frameParameters (st.frames i) := by
      unfold child
      split
      · exact (observe_changeFrame frameParameters admitted (t+1) _ rfl i).trans (ha i)
      · exact ha i
    have hf (i : ℕ) : frameParameters (final.frames i) = frameParameters (st.frames i) := by
      unfold final
      split <;> exact hc i
    unfold prepared
    split
    · exact hf i
    · exact hb i
  have hrefresh : frameParameters ((refreshKeys g prepared (insert v (g.neighbors v).toFinset)).frames i) =
      frameParameters (prepared.frames i) := by
    by_cases hh : i ≤ prepared.top <;> simp [refreshKeys,hh,frameParameters]
  unfold exteriorPush frameParameters
  change frameParameters ((refreshKeys g prepared (insert v (g.neighbors v).toFinset)).frames i) = _
  exact hrefresh.trans (hprepared i)

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.DepthInvariant

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma top_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).top = if P then a.top else b.top := by split <;> rfl
@[simp] lemma top_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) : (debit st j w).top = st.top := rfl
@[simp] lemma top_changeFrame (st : RecursiveState n) (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) :
    (changeFrame st j f).top = st.top := rfl
@[simp] lemma top_changePC (st : RecursiveState n) (pc : NormalizePC) : (changePC st pc).top = st.top := rfl
@[simp] lemma top_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).top = st.top := rfl
@[simp] lemma top_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).top = st.top := rfl
@[simp] lemma top_finish (st : RecursiveState n) : (finishEpisode st).top = st.top := rfl
@[simp] lemma top_complete (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (st : RecursiveState n) : (completeComponent m g s α st).top = st.top := rfl
@[simp] lemma top_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).top = if st.top = 0 then st.top else st.top-1 := by
  unfold endCall
  dsimp only
  split <;> rfl
@[simp] lemma top_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) : (exteriorPush g α st t v).top = st.top := by
  simp [exteriorPush]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallIDs

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma call_ids_transport (st u : RecursiveState n) (hi : CallIDInvariant st)
    (ht : u.top ≤ st.top) (hn : u.nextId = st.nextId)
    (hf : ∀ i ≤ u.top, (u.frames i).id = (st.frames i).id) : CallIDInvariant u := by
  refine ⟨(hf 0 (Nat.zero_le _)).trans hi.1,by simpa [hn] using hi.2.1,?_⟩
  intro i hh hn0
  rw [hf i hh]
  exact hi.2.2 i (hh.trans ht) hn0

lemma call_ids_metadata (st : RecursiveState n) (hi : CallIDInvariant st)
    (j : ℕ) (f : NormalizeFrame n → NormalizeFrame n) (hid : (f (st.frames j)).id = (st.frames j).id) :
    CallIDInvariant (changeFrame st j f) :=
  call_ids_transport st _ hi le_rfl rfl (fun i _ => observe_changeFrame (fun f => f.id) st j f hid i)

lemma call_ids_PC (st : RecursiveState n) (pc : NormalizePC) (hi : CallIDInvariant st) :
    CallIDInvariant (changePC st pc) := call_ids_metadata st hi st.top _ rfl

lemma call_ids_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : CallIDInvariant st) : CallIDInvariant (exteriorPush g α st t v) := by
  refine call_ids_transport st (exteriorPush g α st t v) hi (by simp) ?_ ?_
  · simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> rfl
  · intro i _
    exact congrArg (fun z => z.2.2.2.2.2.2) (exterior_parameters g α st t v i)

lemma call_ids_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : CallIDInvariant st) : CallIDInvariant (jointUpdate g α st h) := by
  refine call_ids_transport st (jointUpdate g α st h) hi le_rfl rfl ?_
  intro i _
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]

lemma call_ids_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : CallIDInvariant st) : CallIDInvariant (refreshKeys g st T) := by
  refine call_ids_transport st (refreshKeys g st T) hi le_rfl rfl ?_
  intro i _
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]

lemma call_ids_finish (st : RecursiveState n) (hi : CallIDInvariant st) :
    CallIDInvariant (finishEpisode st) := by
  unfold finishEpisode
  apply call_ids_metadata
  · exact hi
  · rfl

lemma call_ids_new (st : RecursiveState n) (c : NormalizeFrame n) (hi : CallIDInvariant st)
    (hid : c.id = st.nextId) : CallIDInvariant
      {st with top := st.top+1,nextId := st.nextId+1,frames := Function.update st.frames (st.top+1) c} := by
  refine ⟨?_,by dsimp; omega,?_⟩
  · have hne : 0 ≠ st.top+1 := by omega
    simpa [hne] using hi.1
  · intro i hh hn
    change i ≤ st.top+1 at hh
    by_cases he : i = st.top+1
    · subst i
      simpa [hid] using hi.2.1
    · simpa [he] using hi.2.2 i (by omega) hn

lemma call_ids_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : CallIDInvariant st) :
    CallIDInvariant (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · exact hi
  · exact call_ids_transport st _ hi (Nat.sub_le _ _) rfl (fun _ _ => rfl)

lemma call_ids_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    CallIDInvariant (recursiveInit g s q ℓ schedule) := by
  refine ⟨?_,by simp [recursiveInit],?_⟩
  · simp [recursiveInit,freshFrame,emptyFrame]
  · intro i hi hn
    change i ≤ 0 at hi
    omega

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.CallIDStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma call_ids_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : CallIDInvariant st) (pc : NormalizePC) :
    CallIDInvariant (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact call_ids_PC _ pc hi
  · cases hp : pendingPush st with
    | none => exact call_ids_PC _ pc hi
    | some p => obtain ⟨t,v⟩ := p; exact call_ids_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma call_ids_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n)
    (hi : CallIDInvariant st) : CallIDInvariant (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]
    exact hi
  simp only [hc,ite_false]
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · exact call_ids_drain g α st hi _
      · split <;> exact call_ids_PC _ _ hi
  | beginEpisode =>
    simp only [hpc]
    apply call_ids_metadata _ _ st.top _ rfl
    exact hi
  | fullSolve =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · apply call_ids_PC _ _
        unfold CallIDInvariant
        exact call_ids_refresh g _ (touchedBy g (st.frames st.top).active)
          (call_ids_joint g α st _ hi)
      · exact hi
  | normalize =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · exact call_ids_PC _ _ hi
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode+1})
        have hup : CallIDInvariant up := call_ids_metadata u hi st.top _ rfl
        exact call_ids_new up c hup (by simp [c,freshFrame,up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · cases hp : pendingPush st with
        | none => exact call_ids_PC _ _ hi
        | some p => obtain ⟨t,v⟩ := p; exact call_ids_exterior g α st t v hi
      · split
        · exact call_ids_PC _ _ hi
        · split
          · let C := (st.frames st.top).cache ∪ (st.frames st.top).high
            let u := changeFrame st st.top (fun fc => {fc with cache := C})
            have hu : CallIDInvariant u := call_ids_metadata st hi st.top _ rfl
            unfold CallIDInvariant
            exact call_ids_refresh g _ (touchedBy g C) (call_ids_joint g α u _ hu)
          · exact hi
  | afterChild =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ (call_ids_finish _ hi)
    · split
      · exact call_ids_PC _ _ (call_ids_finish _ hi)
      · exact call_ids_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ (call_ids_finish _ hi)
    · split
      · exact call_ids_PC _ _ (call_ids_finish _ hi)
      · apply call_ids_metadata _ _ st.top _ rfl
        exact call_ids_finish _ hi
  | restartDrain =>
    simp only [hpc]
    split
    · exact call_ids_PC _ _ hi
    · split
      · exact call_ids_drain g α st hi _
      · exact call_ids_metadata (debit st st.top 1) hi st.top
          (fun fc => {fc with needFull := true, pc := .beginEpisode}) rfl
  | normal =>
    simp only [hpc]
    exact call_ids_end g α _ hi
  | interrupted =>
    simp only [hpc]
    exact call_ids_end g α _ hi

lemma call_ids_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CallIDInvariant (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using call_ids_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using call_ids_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.ExteriorStages

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}


lemma exterior_stages (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    let δ := min ((st.frames t).residual v/(5*LocalPush.deg g.graph v))
      (3*(st.frames t).q/8-relative st t v)
    let base := rawExterior g α st t v δ
    let u := if relative st t v+δ = 3*(st.frames t).q/8 then admitStage g base t v else base
    exteriorPush g α st t v = debit (refreshKeys g u (insert v (g.neighbors v).toFinset)) t
      (32*(st.top+1)*((g.neighbors v).length+1)*keyCost (refreshKeys g u (insert v (g.neighbors v).toFinset)) : ℕ) := by
  classical
  dsimp only
  unfold exteriorPush admitStage
  by_cases ht : t ≤ st.top <;> simp only [rawExterior,ht,ite_true,ite_false] <;> rfl

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootCharges

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma root_charge_debit (st : RecursiveState n) (hi : RootChargeInvariant st)
    (hid : (st.frames 0).id = 0) (j : ℕ) (w : ℝ≥0∞) :
    RootChargeInvariant (debit st j w) := by
  have he : ∃ i ≤ j, (st.frames i).id = 0 := ⟨0,Nat.zero_le _,hid⟩
  simpa [RootChargeInvariant,debit,he] using congrArg (fun c => c+w) hi

lemma root_charge_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : RootChargeInvariant st) : RootChargeInvariant (refreshKeys g st T) := hi

lemma root_charge_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : RootChargeInvariant st) (hid : (st.frames 0).id = 0) :
    RootChargeInvariant (endCall g α st) := by
  unfold endCall
  dsimp only
  split
  · exact root_charge_debit _ hi hid _ _
  · exact hi

lemma root_closed_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (hi : RootClosedInvariant st) (hid : CallIDInvariant st) :
    RootClosedInvariant (endCall g α st) := by
  classical
  unfold endCall
  dsimp only
  split
  · rename_i ht
    simp [RootClosedInvariant,ht,hid.1,debit]
  · rename_i ht
    have hp := hid.2.2 st.top le_rfl ht
    have hn : 0 ≠ (st.frames st.top).id := by omega
    simpa [RootClosedInvariant,hn] using hi

lemma root_closed_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (hid : (st.frames 0).id = 0) :
    RootClosedInvariant (completeComponent m g s α st) := by
  classical
  have he : 0 ∈ (Finset.range (st.top+1)).image (fun i => (st.frames i).id) := by
    apply Finset.mem_image.mpr
    exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _),hid⟩
  simp [RootClosedInvariant,completeComponent,debit,he]

lemma root_account_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    RootChargeInvariant (recursiveInit g s q ℓ schedule) ∧
    RootClosedInvariant (recursiveInit g s q ℓ schedule) := by
  simp [RootChargeInvariant,RootClosedInvariant,recursiveInit]

lemma root_charge_admit (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : RootChargeInvariant st) : RootChargeInvariant (admitStage g st t v) := by
  simp [RootChargeInvariant,admitStage,changeFrame] <;> (try split_ifs) <;> exact hi

lemma root_charge_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : RootChargeInvariant st) (hid : CallIDInvariant st) :
    RootChargeInvariant (exteriorPush g α st t v) := by
  have hh := (call_ids_exterior g α st t v hid).1
  rw [exterior_stages] at hh ⊢
  apply root_charge_debit
  · apply root_charge_refresh
    split
    · apply root_charge_admit
      exact hi
    · exact hi
  · exact hh

lemma root_closed_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : RootClosedInvariant st) : RootClosedInvariant (exteriorPush g α st t v) := by
  simp [RootClosedInvariant,exteriorPush,refreshKeys,debit,changeFrame] <;> (try split_ifs) <;> exact hi

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootLedger

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma ledger_debit (st : RecursiveState n) (hi : RootLedger st) (j : ℕ) (w : ℝ≥0∞) :
    RootLedger (debit st j w) := ⟨hi.1,root_charge_debit st hi.2.1 hi.1.1 j w,hi.2.2⟩

lemma ledger_metadata (st : RecursiveState n) (hi : RootLedger st) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) (hid : (f (st.frames j)).id = (st.frames j).id) :
    RootLedger (changeFrame st j f) := ⟨call_ids_metadata st hi.1 j f hid,hi.2⟩

lemma ledger_PC (st : RecursiveState n) (pc : NormalizePC) (hi : RootLedger st) :
    RootLedger (changePC st pc) := ledger_metadata st hi st.top _ rfl

lemma ledger_finish (st : RecursiveState n) (hi : RootLedger st) : RootLedger (finishEpisode st) := by
  exact ⟨call_ids_finish st hi.1,hi.2⟩

lemma ledger_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n)
    (hi : RootLedger st) : RootLedger (exteriorPush g α st t v) :=
  ⟨call_ids_exterior g α st t v hi.1,root_charge_exterior g α st t v hi.2.1 hi.1,
    root_closed_exterior g α st t v hi.2.2⟩

lemma ledger_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ)
    (hi : RootLedger st) : RootLedger (jointUpdate g α st h) := ⟨call_ids_joint g α st h hi.1,hi.2⟩

lemma ledger_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n))
    (hi : RootLedger st) : RootLedger (refreshKeys g st T) := ⟨call_ids_refresh g st T hi.1,hi.2⟩

lemma ledger_new (st : RecursiveState n) (c : NormalizeFrame n) (hi : RootLedger st)
    (hid : c.id = st.nextId) : RootLedger
      {st with top := st.top+1,nextId := st.nextId+1,frames := Function.update st.frames (st.top+1) c} :=
  ⟨call_ids_new st c hi.1 hid,hi.2⟩

lemma ledger_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : RootLedger st) :
    RootLedger (endCall g α st) :=
  ⟨call_ids_end g α st hi.1,root_charge_end g α st hi.2.1 hi.1.1,root_closed_end g α st hi.2.2 hi.1⟩

lemma ledger_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) (hi : RootLedger st) : RootLedger (completeComponent m g s α st) := by
  refine ⟨hi.1,?_,root_closed_complete m g s α st hi.1.1⟩
  exact root_charge_debit st hi.2.1 hi.1.1 _ _

lemma ledger_init (g : InputGraph n) (s : Fin n) (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) :
    RootLedger (recursiveInit g s q ℓ schedule) :=
  ⟨call_ids_init g s q ℓ schedule,root_account_init g s q ℓ schedule⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootLedgerStep

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma ledger_drain (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (hi : RootLedger st) (pc : NormalizePC) :
    RootLedger (if anyExhausted st then changePC (debit st st.top 1) pc else
      match pendingPush st with
      | some (t,v) => exteriorPush g α st t v
      | none => changePC (debit st st.top 1) pc) := by
  split
  · exact ledger_PC _ pc (ledger_debit st hi _ _)
  · cases hp : pendingPush st with
    | none => exact ledger_PC _ pc (ledger_debit st hi _ _)
    | some p => obtain ⟨t,v⟩ := p; exact ledger_exterior g α st t v hi

set_option maxHeartbeats 1000000 in
lemma ledger_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : RootLedger st) :
    RootLedger (recursiveStep m g s α ℓ schedule st) := by
  classical
  by_cases hd : st.done = true
  · simpa [recursiveStep,hd] using hi
  simp only [recursiveStep,hd,Bool.false_eq_true,ite_false]
  by_cases hc : componentComplete st
  · simp only [hc,ite_true]; exact ledger_complete m g s α st hi
  simp only [hc,ite_false]
  have hcheap := ledger_debit st hi st.top 1
  cases hpc : (st.frames st.top).pc with
  | initialDrain =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ hcheap
    · split
      · exact ledger_drain g α st hi _
      · split <;> exact ledger_PC _ _ hcheap
  | beginEpisode =>
    simp only [hpc]
    apply ledger_metadata
    · exact ledger_debit st hi _ _
    · rfl
  | fullSolve =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ hcheap
    · split
      · apply ledger_PC
        exact ledger_debit _ (ledger_refresh g _ _ (ledger_joint g α st _ hi)) _ _
      · exact hcheap
  | normalize =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ hcheap
    · split
      · exact ledger_PC _ _ hcheap
      · let c := freshFrame g schedule ℓ (st.top+1) st.nextId (st.frames st.top).block
          (st.frames st.top).theta (st.frames st.top).active st.x (st.frames st.top).residual
        let u := debit st st.top (16*(volumeNat g (st.frames st.top).active+1)*keyCost st+
          8*(ℓ+2)*((st.frames st.top).block+2) : ℕ)
        let up := changeFrame u st.top (fun fc =>
          {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
        have hu : RootLedger u := ledger_debit st hi _ _
        have hup : RootLedger up := ledger_metadata u hu st.top _ rfl
        exact ledger_new up c hup (by simp [c,freshFrame,up,u,changeFrame,debit])
  | leafDrain =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ hcheap
    · split
      · cases hp : pendingPush st with
        | none => exact ledger_PC _ _ hcheap
        | some p => obtain ⟨t,v⟩ := p; exact ledger_exterior g α st t v hi
      · split
        · exact ledger_PC _ _ hcheap
        · split
          · apply ledger_debit
            apply ledger_refresh
            apply ledger_joint
            exact ledger_metadata st hi st.top _ rfl
          · exact hcheap
  | afterChild =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ (ledger_finish _ hcheap)
    · split
      · exact ledger_PC _ _ (ledger_finish _ hcheap)
      · exact ledger_drain g α st hi _
  | finishEpisode =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ (ledger_finish _ hcheap)
    · split
      · exact ledger_PC _ _ (ledger_finish _ hcheap)
      · apply ledger_metadata
        · exact ledger_finish _ (ledger_debit st hi _ _)
        · rfl
  | restartDrain =>
    simp only [hpc]
    split
    · exact ledger_PC _ _ hcheap
    · split
      · exact ledger_drain g α st hi _
      · exact ledger_metadata _ hcheap st.top _ rfl
  | normal => simp only [hpc]; exact ledger_end g α _ hcheap
  | interrupted => simp only [hpc]; exact ledger_end g α _ hcheap

lemma ledger_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootLedger (recursiveRun m g s α q ℓ schedule t) := by
  induction t with
  | zero => simpa [recursiveRun] using ledger_init g s q ℓ schedule
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using ledger_step m g s α ℓ schedule _ ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootInformation

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

@[simp] lemma information_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (t : ℕ) (v : Fin n) :
    (exteriorPush g α st t v).information = st.information := by
  simp [exteriorPush,changeFrame,refreshKeys,debit] <;> (try split_ifs) <;> rfl

@[simp] lemma information_debit (st : RecursiveState n) (j : ℕ) (w : ℝ≥0∞) :
    (debit st j w).information = st.information := rfl
@[simp] lemma information_changeFrame (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) : (changeFrame st j f).information = st.information := rfl
@[simp] lemma information_PC (st : RecursiveState n) (pc : NormalizePC) :
    (changePC st pc).information = st.information := rfl
@[simp] lemma information_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n) (h : Fin n → ℝ) :
    (jointUpdate g α st h).information = st.information := rfl
@[simp] lemma information_refresh (g : InputGraph n) (st : RecursiveState n) (T : Finset (Fin n)) :
    (refreshKeys g st T).information = st.information := rfl
@[simp] lemma information_finish (st : RecursiveState n) : (finishEpisode st).information = st.information := rfl
@[simp] lemma information_complete (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (st : RecursiveState n) : (completeComponent m g s α st).information = st.information := rfl
@[simp] lemma information_end (g : InputGraph n) (α : ℝ) (st : RecursiveState n) :
    (endCall g α st).information = st.information := by unfold endCall; dsimp only; split <;> rfl
@[simp] lemma information_ite (P : Prop) [Decidable P] (a b : RecursiveState n) :
    (if P then a else b).information = if P then a.information else b.information := by split <;> rfl

set_option maxHeartbeats 1000000 in
lemma root_information_step (m : SolveModel) (g : InputGraph n) (s : Fin n) (α : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) (hi : CallIDInvariant st) :
    (recursiveStep m g s α ℓ schedule st).information 0 = st.information 0 := by
  classical
  have hn : 0 ≠ st.nextId := by have := hi.2.1; omega
  cases hp : pendingPush st with
  | none =>
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,freshFrame,hn] <;> (try split_ifs) <;> simp_all
  | some p =>
    obtain ⟨t,v⟩ := p
    cases hpc : (st.frames st.top).pc <;>
      simp [recursiveStep,hpc,hp,freshFrame,hn] <;> (try split_ifs) <;> simp_all

lemma root_information_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).information 0 =
      some ⟨0,1/q,blockScale schedule ℓ 0 (1/q)⟩ := by
  induction t with
  | zero => simp [recursiveRun,recursiveInit,freshFrame]
  | succ t ih =>
    simpa only [recursiveRun,Function.iterate_succ_apply'] using
      (root_information_step m g s α ℓ schedule _ (call_ids_run m g s α q ℓ schedule t)).trans ih

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootWorkEnvelope

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}

lemma recursiveWork_eq_root_callWork (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) :
    recursiveWork m g s α ε ℓ schedule = callWork m g s α ε ℓ schedule 0 := by
  classical
  unfold recursiveWork callWork
  dsimp only
  have he : (∃ t, (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).done = true) ↔
      ∃ t, 0 ∈ (recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule t).closed := by
    constructor <;> rintro ⟨t,ht⟩ <;> refine ⟨t,?_⟩
    · exact (ledger_run m g s α (rootThreshold ε ℓ) ℓ schedule t).2.2.mpr ht
    · exact (ledger_run m g s α (rootThreshold ε ℓ) ℓ schedule t).2.2.mp ht
  simp only [he]
  split
  · congr 1
    funext t
    exact (ledger_run m g s α (rootThreshold ε ℓ) ℓ schedule t).2.1
  · rfl

lemma recursiveWork_le_workEnvelope (m : SolveModel) (g : InputGraph n) (s : Fin n) (α ε : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (hα : 0 < α ∧ α ≤ 1/2) (hs : 0 < g.graph.degree s) :
    recursiveWork m g s α ε ℓ schedule ≤
      workEnvelope m ε ℓ schedule 0 (1/rootThreshold ε ℓ) := by
  rw [recursiveWork_eq_root_callWork]
  apply le_sSup
  exact ⟨n,g,s,α,0,0,hα.1,hα.2,hs,
    root_information_run m g s α (rootThreshold ε ℓ) ℓ schedule 0,rfl⟩

lemma root_termination_of_closure (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule)
    (hclose : ∃ t, 0 ∈ (recursiveRun m g s α q ℓ schedule t).closed) :
    ∃ t, (recursiveRun m g s α q ℓ schedule t).done = true := by
  obtain ⟨t,ht⟩ := hclose
  exact ⟨t,(ledger_run m g s α q ℓ schedule t).2.2.mp ht⟩

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.Subpolynomial

set_option autoImplicit false
open Filter Topology
namespace NearlyOptimalPPR.Computation

lemma sqrt_log_ratio_limit :
    Tendsto (fun t : ℝ => Real.sqrt ((Real.log 2 + t) * Real.log (Real.log 4 + t)) / t)
      atTop (𝓝 0) := by
  have hc (a : ℝ) : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hr (a : ℝ) : Tendsto (fun t : ℝ => (a+t)/t) atTop (𝓝 1) := by
    have hh := (hc a).add_const 1
    have hh' : Tendsto (fun t : ℝ => a/t+1) atTop (𝓝 1) := by simpa using hh
    apply hh'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [add_div, ht.ne']
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log 4+t)/t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-Real.log 4) 1 one_ne_zero).comp
      (show Tendsto (fun t : ℝ => Real.log 4 + t) atTop atTop from
        tendsto_const_nhds.add_atTop tendsto_id)
    convert! hh using 1
    ext t
    simp
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ((hr (Real.log 2)).mul hll)
  simp only [one_mul, Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hprod : 0 ≤ (Real.log 2 + t) * Real.log (Real.log 4 + t) := by
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  simp only [Function.comp_apply]
  rw [show ((Real.log 2+t)/t) * (Real.log (Real.log 4+t)/t) =
    ((Real.log 2+t)*Real.log (Real.log 4+t))/(t^2) by ring]
  rw [Real.sqrt_div hprod, Real.sqrt_sq ht0.le]

theorem subpolynomial_envelope (C c : ℝ) (hC : 0 < C) : subpolynomialEnvelope C c := by
  intro η hη
  have hl : Tendsto (fun t : ℝ => Real.log C / t +
      c * (Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))/t)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds.div_atTop tendsto_id (a := Real.log C)).add
      (sqrt_log_ratio_limit.const_mul c)
    simpa using hh
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hl.eventually_lt_const hη)
  let B := max T 1
  let ε₀ := Real.exp (-B)
  have hB : 1 ≤ B := le_max_right _ _
  have hε₀ : 0 < ε₀ := Real.exp_pos _
  have hε₀one : ε₀ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    dsimp [B]
    linarith [le_max_right T 1]
  refine ⟨ε₀, hε₀, hε₀one, ?_⟩
  intro ε hε hsmall
  let t := Real.log (1/ε)
  have htlog : t = -Real.log ε := by
    dsimp [t]
    rw [Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub]
  have hlogε : Real.log ε ≤ -B := by
    have hh := Real.log_le_log hε hsmall
    simpa only [ε₀, Real.log_exp] using hh
  have htB : B ≤ t := by rw [htlog]; linarith
  have htpos : 0 < t := by linarith
  have htT : T ≤ t := (le_max_left _ _).trans htB
  have hbound := hT t htT
  have halg : Real.log C / t + c * (Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))/t) =
      (Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t)))/t := by ring
  rw [halg] at hbound
  have hexponent : Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t)) ≤ η*t :=
    ((div_lt_iff₀ htpos).mp hbound).le
  have h2 : Real.log (2/ε) = Real.log 2+t := by
    rw [Real.log_div (by norm_num) hε.ne', htlog]
    ring
  have h4 : Real.log (4/ε) = Real.log 4+t := by
    rw [Real.log_div (by norm_num) hε.ne', htlog]
    ring
  have hK : 0 < 1/ε := by positivity
  calc
    envelope C c ε = (1/ε) * Real.exp
        (Real.log C + c * Real.sqrt ((Real.log 2+t)*Real.log (Real.log 4+t))) := by
      rw [envelope, h2, h4, Real.exp_add, Real.exp_log hC]
      ring
    _ ≤ (1/ε) * Real.exp (η*t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hK.le
    _ = (1/ε) ^ (1+η) := by
      rw [Real.rpow_add hK, Real.rpow_one, Real.rpow_def_of_pos hK]
      congr 2
      ring

end NearlyOptimalPPR.Computation

-- Proof module: Solutions.RootControl

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma frame_pc_debit (st : RecursiveState n) (j i : ℕ) (w : ℝ≥0∞) :
    ((debit st j w).frames i).pc = (st.frames i).pc := by simp [debit]
@[simp] lemma frame_pc_refresh (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) (i : ℕ) :
    ((refreshKeys g st T).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [refreshKeys,he]
@[simp] lemma frame_pc_joint (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) (i : ℕ) :
    ((jointUpdate g α st h).frames i).pc = (st.frames i).pc := by
  by_cases he : i ≤ st.top <;> simp [jointUpdate,he]
@[simp] lemma frame_pc_ite (P : Prop) [Decidable P] (a b : RecursiveState n) (i : ℕ) :
    ((if P then a else b).frames i).pc = if P then (a.frames i).pc else (b.frames i).pc := by
  split <;> rfl
@[simp] lemma frame_pc_changeFrame (st : RecursiveState n) (j i : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) :
    ((changeFrame st j f).frames i).pc =
      if i = j then (f (st.frames j)).pc else (st.frames i).pc := by
  by_cases he : i = j <;> simp [changeFrame,he]

@[simp] lemma frame_pc_exterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (i : ℕ) :
    ((exteriorPush g α st t v).frames i).pc = (st.frames i).pc := by
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let h := min (f.residual v/(5*d)) (3*f.q/8-relative st t v)
  let base : RecursiveState n :=
    {st with
      x := Function.update st.x v (st.x v+h)
      stored := insert v st.stored
      frames := fun i => if i ≤ st.top then
        let fi := st.frames i
        {fi with
          residual := fun w => fi.residual w +
          (if w = v then if i < t then -d*h else if i = t then -5*d*h else 0 else 0) +
          (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*h else 0)
          W := fi.W + if fi.openBudget = true ∧ t ≤ i then (1-α)*d*h else 0}
        else st.frames i}
  let admitted := changeFrame base t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let child := if t < st.top then changeFrame admitted (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (admitted.x v)
      residual := Function.update fc.residual v ((admitted.frames t).residual v)}) else admitted
  let final := if t = 0 then {child with boundaryEdges := st.boundaryEdges +
    (g.neighbors v).length - 2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else child
  have hb (i : ℕ) : (base.frames i).pc = (st.frames i).pc := by
    by_cases hi : i ≤ st.top <;> simp [base,hi]
  have ha (i : ℕ) : (admitted.frames i).pc = (st.frames i).pc := by
    simp only [admitted,frame_pc_changeFrame]
    split <;> simp_all [hb]
  have hc (i : ℕ) : (child.frames i).pc = (st.frames i).pc := by
    unfold child
    split
    · simp only [frame_pc_changeFrame]
      split <;> simp_all [ha]
    · exact ha i
  have hf (i : ℕ) : (final.frames i).pc = (st.frames i).pc := by
    unfold final
    split <;> exact hc i
  unfold exteriorPush
  simp only [frame_pc_debit,frame_pc_refresh]
  change ((if relative st t v+h = 3*f.q/8 then final else base).frames i).pc = _
  split
  · exact hf i
  · exact hb i

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.UniformFullCount

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma root_threshold_unit (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    0 < rootThreshold ε ℓ ∧ rootThreshold ε ℓ ≤ 1 := by
  have he : 0 < ε := hε.1
  have hk : (3 : ℝ) ≤ (kappa ℓ 0 : ℝ) := by
    exact_mod_cast (show 3 ≤ kappa ℓ 0 by simp only [kappa,Nat.sub_zero]; omega)
  unfold rootThreshold
  refine ⟨by positivity,?_⟩
  apply (div_le_one (by positivity : 0 < 32*(kappa ℓ 0 : ℝ))).mpr
  linarith [hε.2]

end
end NearlyOptimalPPR.Computation

-- Proof module: Solutions.OverheadMonotone

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma overhead_base_one (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    1 ≤ 2+Real.log (2/ε)+(ℓ : ℝ) := by
  have hL := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
  have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  linarith

lemma overhead_mono (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ a b : ℕ) (C D : ℝ)
    (hC : 0 ≤ C) (hCD : C ≤ D) (hab : a ≤ b) : overhead C a ε ℓ ≤ overhead D b ε ℓ := by
  have hX := overhead_base_one ε hε ℓ
  unfold overhead
  calc
    _ ≤ C*(2+Real.log (2/ε)+(ℓ : ℝ))^b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hab) hC
    _ ≤ _ := mul_le_mul_of_nonneg_right hCD (by positivity)

lemma overhead_one (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ c : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    1 ≤ overhead C c ε ℓ := by
  have hX := one_le_pow₀ (overhead_base_one ε hε ℓ) (n:=c)
  unfold overhead
  exact one_le_mul_of_one_le_of_one_le hC hX

end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal
noncomputable section

theorem solution (m : SolveModel) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ subpolynomialEnvelope C c ∧
      ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α ≤ 1/2 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
        let ℓ := balancedDepth ε
        recursiveWork m g s α ε ℓ [] ≤ ENNReal.ofReal (envelope C c ε) ∧
          ∃ t, (recursiveRun m g s α (rootThreshold ε ℓ) ℓ [] t).done=true := by
  obtain ⟨Cr,cr,hCr,hcr,hLevel⟩ := recursive_level_work m
  let C := Cr+1
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  obtain ⟨c,hc,hEnvelope⟩ := balanced_recurrence_envelope C cr hC
  refine ⟨1,c,by norm_num,hc,subpolynomial_envelope 1 c (by norm_num),?_⟩
  intro n g s α ε ha ha1 he he1 hs ℓ
  let P := overhead C cr ε ℓ
  let N := 1/rootThreshold ε ℓ
  have hq := root_threshold_unit ε ⟨he,he1⟩ ℓ
  have hN : 1 ≤ N := (le_div_iff₀ hq.1).mpr (by simpa using hq.2)
  have hP : 1 ≤ P := overhead_one ε ⟨he,he1⟩ ℓ cr C hC
  have hm := overhead_mono ε ⟨he,he1⟩ ℓ cr cr Cr C hCr.le (by dsimp only [C]; linarith) le_rfl
  obtain ⟨_,hStep,hLeaf⟩ := hLevel ε ℓ [] he he1
  have hstep (j : ℕ) (A : ℝ) (hj : j < ℓ) (hA : 1 ≤ A) :
      let b := blockScale [] ℓ j A
      workEnvelope m ε ℓ [] j A ≤ ENNReal.ofReal P*(ENNReal.ofReal (A^2/b)+
        ENNReal.ofReal (A/b)*workEnvelope m ε ℓ [] (j+1) b)+ENNReal.ofReal (P*A) := by
    intro b
    apply (hStep j A hj hA).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hm) (by positivity)
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hm (by linarith))
  have hleaf (A : ℝ) (hA : 1 ≤ A) :
      let b := blockScale [] ℓ ℓ A
      workEnvelope m ε ℓ [] ℓ A ≤ ENNReal.ofReal (P*(A^2/b+A*b)) := by
    intro b
    apply (hLeaf A hA).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right hm
    exact add_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (by linarith) (Nat.cast_nonneg _))
  have hbalanced := balanced_recurrence (fun j A => workEnvelope m ε ℓ [] j A) ℓ P hP hleaf hstep ℓ 0
    (by omega) N hN
  have henvelope := hEnvelope ε he he1
  have hroot := recursiveWork_le_workEnvelope m g s α ε ℓ [] ⟨ha,ha1⟩ hs
  refine ⟨hroot.trans (hbalanced.trans (ENNReal.ofReal_le_ofReal ?_)),?_⟩
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using henvelope
  · have hi := root_information_run m g s α (rootThreshold ε ℓ) ℓ [] 0
    obtain ⟨_,_,_,_,hclose⟩ := (hLevel ε ℓ [] he he1).1 n g s α ha ha1 hs 0 0 _ hi
    apply root_termination_of_closure m g s α (rootThreshold ε ℓ) ℓ []
    obtain ⟨t,_,ht⟩ := hclose
    exact ⟨t,ht⟩

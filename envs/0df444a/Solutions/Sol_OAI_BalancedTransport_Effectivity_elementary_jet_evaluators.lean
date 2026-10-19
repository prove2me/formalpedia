-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.elementary_jet_evaluators
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:55:00.704701+00:00
-- url     : https://prove2.me/submissions/97eb1d40-fa47-4e6d-a8d1-64ab0f522c81

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveGluing.lean:L149-L221
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.elementary_jet_evaluators. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing
import Theorems.Thm_OAI_BalancedTransport_Effectivity_ElementaryScalar_spaceD
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_computable_bound
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_computable_rational
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_differentiableAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_estimate
import Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_hasDerivAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_foldl
import Theorems.Thm_OAI_BalancedTransport_Effectivity_fieldArgs_time_hasDerivAt
import Theorems.Thm_OAI_BalancedTransport_Effectivity_log_abs_bound
import Theorems.Thm_OAI_BalancedTransport_Effectivity_nat_mul_error_shift
import Theorems.Thm_OAI_BalancedTransport_Effectivity_rhoCoeffs_spec

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma rhoJet_zero_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) : rhoJet n x = 0 := by
  simp [rhoJet, expNegInvGlue.zero_of_nonpos hx]

lemma inv_pow_mul_rho_le {x : ℝ} (hx : 0 < x) (j k : ℕ) :
    x⁻¹ ^ j * expNegInvGlue x ≤ ((j + k).factorial : ℝ) * x ^ k := by
  have hf : (0 : ℝ) < (j + k).factorial := by positivity
  have he := Real.pow_div_factorial_le_exp x⁻¹ (inv_nonneg.mpr hx.le) (j + k)
  have hdiv : x⁻¹ ^ (j + k) / Real.exp x⁻¹ ≤ ((j + k).factorial : ℝ) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    simpa [mul_comm] using (div_le_iff₀ hf).mp he
  have hid : x⁻¹ ^ j * expNegInvGlue x =
      (x⁻¹ ^ (j + k) / Real.exp x⁻¹) * x ^ k := by
    rw [expNegInvGlue, ite_eq_right hx.not_ge, Real.exp_neg, pow_add]
    field_simp
    simp [inv_mul_cancel₀ (pow_ne_zero k hx.ne')]
  rw [hid]
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg hx.le _)

lemma polynomial_rho_seam_bound (p : Polynomial ℤ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |p.eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x| ≤
      (rhoWeight p k : ℝ) * x ^ k := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  calc
    |∑ j ∈ p.support, (Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| ≤
        ∑ j ∈ p.support, |(Int.castRingHom ℝ) (p.coeff j) * x⁻¹ ^ j * expNegInvGlue x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) * (x⁻¹ ^ j * expNegInvGlue x) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [abs_mul, abs_of_pos hx,
        abs_of_nonneg (expNegInvGlue.nonneg x), mul_assoc]
    _ ≤ ∑ j ∈ p.support, ((p.coeff j).natAbs : ℝ) *
        (((j + k).factorial : ℝ) * x ^ k) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (inv_pow_mul_rho_le hx j k) (Nat.cast_nonneg _)
    _ = (rhoWeight p k : ℝ) * x ^ k := by
      simp [rhoWeight, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma rhoJet_bound (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoWeight (rhoPolynomial n) 0 : ℝ) := by
  by_cases hx : 0 < x
  · simpa [rhoJet] using polynomial_rho_seam_bound (rhoPolynomial n) 0 hx
  · rw [rhoJet_zero_of_nonpos n (le_of_not_gt hx), abs_zero]
    exact Nat.cast_nonneg _

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem JointSmooth.spaceD {f : Field F} (hf : JointSmooth f) (i : Fin 3) :
    JointSmooth (spaceD i f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × Space => f z.1.1 z.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hh.fderiv_apply contDiff_snd contDiff_const (by simp)

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FieldBounds ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma JointSmooth.fullMixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex) :
    JointSmooth (fullMixedD a v) := by
  induction a with
  | nil => exact hv
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD i

lemma JointSmooth.timeSlice {v : Field F} (hv : JointSmooth v) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => v t x) := hv.comp (contDiff_id.prodMk contDiff_const)

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

lemma getD_zero_of_length_le {cs : List ℤ} {j : ℕ} (h : cs.length ≤ j) :
    cs.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma rhoPolynomial_coeff_zero (n j : ℕ) (h : (rhoCoeffs n).length ≤ j) :
    (rhoPolynomial n).coeff j = 0 := by
  rw [← rhoCoeffs_spec, getD_zero_of_length_le h]

lemma rhoPolynomial_support_subset (n : ℕ) :
    (rhoPolynomial n).support ⊆ Finset.range (rhoCoeffs n).length := by
  intro j hj
  rw [Finset.mem_range]
  by_contra h
  exact (mem_support_iff.mp hj) (rhoPolynomial_coeff_zero _ _ (le_of_not_gt h))

lemma rhoBound_eq (n k : ℕ) : rhoBound n k = rhoWeight (rhoPolynomial n) k := by
  unfold rhoBound rhoWeight
  simp only [rhoCoeffs_spec]
  exact (Finset.sum_subset (rhoPolynomial_support_subset n) (by
    intro j _ hj
    have hz : (rhoPolynomial n).coeff j = 0 := notMem_support_iff.mp hj
    simp [hz])).symm

lemma rhoJet_bound_computable (n : ℕ) (x : ℝ) : |rhoJet n x| ≤ (rhoBound n 0 : ℝ) := by
  rw [rhoBound_eq]
  exact rhoJet_bound n x

lemma rat_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ q.num.natAbs := by
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  have ha : ((q.num.natAbs : ℕ) : ℝ) = |(q.num : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun a : ℤ => (a : ℝ)) (Int.natCast_natAbs q.num)
  rw [← ha]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < q.den)).mpr
    (le_mul_of_one_le_right (by positivity) hden)

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericPrograms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_fin_cases {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {n : ℕ} {i : α → Fin n} {f : Fin n → α → β}
    (hi : Computable i) (hf : ∀ j, Computable (f j)) :
    Computable (fun a => f (i a) a) := by
  have hl : Computable (fun a => List.ofFn (fun j => f j a)) :=
    Computable.list_ofFn hf
  exact ((Primrec.list_getD default).to_comp.comp hl (Primrec.fin_val.to_comp.comp hi)).of_eq
    (fun a => by simp)

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ComputabilityRules ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ComputableRules
attribute [fun_prop] Computable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

lemma flatMapList [Inhabited β] {f : α → List β} {g : α → β → List γ} (hf : Computable f)
    (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (f a).flatMap (g a)) := by
  have h := computable_foldl hf (Computable.const ([] : List γ))
    (h := fun a p => p.1 ++ g a p.2) (by change Computable (fun p : α × (List γ × β) => _); fun_prop)
  apply h.of_eq
  intro a
  have hh : ∀ (l : List β) (s : List γ), l.foldl (fun s b => s ++ g a b) s = s ++ l.flatMap (g a) := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => intro s; simp only [List.foldl_cons, List.flatMap_cons, ih, List.append_assoc]
  simpa using hh (f a) []

end BalancedTransport.Effectivity.ComputableRules
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma exp_nat_bound (n : ℕ) : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
  rw [← mul_one (n : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericEvaluation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

lemma magnitude (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (C : ℕ) (s : List ℝ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |x i| ≤ C) (hb : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ))
    (hv : Valid o s) : |real d o x s| ≤ ((bound o C b).1 : ℝ) := by
  rcases o with ⟨j,r,a,b'⟩
  have hA := hb a
  have hB := hb b'
  fin_cases j <;>
    dsimp +instances only [real, bound, boundCase, tag, rat, left, right, Valid] at hv ⊢
  · exact rat_abs_le_num r
  · exact hi _
  · simpa only [Nat.cast_add] using (abs_add_le _ _).trans (add_le_add hA hB)
  · simpa only [Nat.cast_mul, abs_mul] using mul_le_mul hA hB (abs_nonneg _) (by positivity)
  · simpa only [abs_neg] using hA
  · have hh := hv rfl
    have hpos : (0 : ℝ) < ((b' + 1 : ℕ) : ℝ)⁻¹ := by positivity
    rw [abs_inv, abs_of_pos (hpos.trans_le hh)]
    simpa only [inv_inv] using inv_anti₀ hpos hh
  · exact rhoJet_bound_computable _ _
  · rw [abs_of_pos (Real.exp_pos _), Nat.cast_pow, Nat.cast_ofNat]
    exact (Real.exp_le_exp.mpr (le_abs_self _ |>.trans hA)).trans (exp_nat_bound _)
  · split_ifs with hr
    · exact log_abs_bound hr
    · simpa only [abs_zero] using (Nat.cast_nonneg (r.num.natAbs + r⁻¹.num.natAbs) (α := ℝ))

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma boundFrom_estimate (p : NumericProgram) (x : Fin d → ℚ) (s : List ℝ)
    (q : List ℚ) (b : List (ℕ × ℕ)) (n C : ℕ) (hi : ∀ i, |(x i : ℝ)| ≤ C)
    (hh : RegisterEstimate n s q b) (hv : p.ValidFrom (fun i => (x i : ℝ)) s) :
    RegisterEstimate n (p.realFrom (fun i => (x i : ℝ)) s) (p.rationalFrom x n q)
      (p.boundFrom C b) := by
  induction p generalizing s q b with
  | nil => exact hh
  | cons o p ih =>
    apply ih _ _ _ ?_ hv.2
    have hb := o.estimate d x n C s q b hi hh hv.1
    constructor
    · intro j
      cases j with
      | zero => exact hb.1
      | succ j => exact hh.magnitude j
    · intro j
      cases j with
      | zero => exact hb.2
      | succ j => exact hh.accuracy j

lemma boundFrom_magnitude (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ)
    (b : List (ℕ × ℕ)) (C : ℕ) (hi : ∀ i, |x i| ≤ C)
    (hh : ∀ j, |s.getD j 0| ≤ ((b.getD j (0,0)).1 : ℝ))
    (hv : p.ValidFrom x s) :
    ∀ j, |(p.realFrom x s).getD j 0| ≤ (((p.boundFrom C b).getD j (0,0)).1 : ℝ) := by
  induction p generalizing s b with
  | nil => exact hh
  | cons o p ih =>
    apply ih _ _ ?_ hv.2
    intro j
    cases j with
    | zero => exact o.magnitude d x C s b hi hh hv.1
    | succ j => exact hh j

lemma approximation_spec (p : NumericProgram) (C : ℕ) (x : Fin d → ℚ) (n : ℕ)
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hv : p.Valid (fun i => (x i : ℝ))) :
    |(p.approximation C x n : ℝ) - p.real (fun i => (x i : ℝ))| ≤ error n := by
  have hb := p.boundFrom_estimate x [] [] [] (n + (p.bound C).2) C hi
    ⟨by simp, by simp⟩ hv
  exact (hb.accuracy 0).trans (nat_mul_error_shift _ _)

lemma magnitude (p : NumericProgram) (C : ℕ) (x : Fin d → ℝ)
    (hi : ∀ i, |x i| ≤ C) (hv : p.Valid x) : |p.real x| ≤ ((p.bound C).1 : ℝ) :=
  p.boundFrom_magnitude x [] [] C hi (by simp) hv 0

lemma computable_rationalStep (d : ℕ) [NeZero d] :
    Computable (fun z : (NumericProgram × (Fin d → ℚ) × ℕ × List ℚ) × (List ℚ × NumericOp) =>
      z.2.2.rational d z.1.2.1 z.1.2.2.1 z.2.1 :: z.2.1) := by
  let A := NumericProgram × (Fin d → ℚ) × ℕ × List ℚ
  have ho : Computable (fun z : A × (List ℚ × NumericOp) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hx : Computable (fun z : A × (List ℚ × NumericOp) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hp : Computable (fun z : A × (List ℚ × NumericOp) => z.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have hs : Computable (fun z : A × (List ℚ × NumericOp) => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hh := (NumericOp.computable_rational d).comp (ho.pair (hx.pair (hp.pair hs)))
  exact Primrec.list_cons.to_comp.comp hh hs

lemma computable_rationalFrom (d : ℕ) [NeZero d] :
    Computable (fun z : NumericProgram × (Fin d → ℚ) × ℕ × List ℚ =>
      rationalFrom z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let A := NumericProgram × (Fin d → ℚ) × ℕ × List ℚ
  have hf : Computable (fun z : A => z.1) := Computable.fst
  have hg : Computable (fun z : A => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact computable_foldl hf hg (computable_rationalStep d).to₂

lemma computable_boundStep : Computable
    (fun z : (NumericProgram × ℕ × List (ℕ × ℕ)) × (List (ℕ × ℕ) × NumericOp) =>
      z.2.2.bound z.1.2.1 z.2.1 :: z.2.1) := by
  let A := NumericProgram × ℕ × List (ℕ × ℕ)
  have ho : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hC : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hs : Computable (fun z : A × (List (ℕ × ℕ) × NumericOp) => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hh := NumericOp.computable_bound.comp (ho.pair (hC.pair hs))
  exact Primrec.list_cons.to_comp.comp hh hs

lemma computable_boundFrom : Computable
    (fun z : NumericProgram × ℕ × List (ℕ × ℕ) => boundFrom z.1 z.2.1 z.2.2) := by
  let A := NumericProgram × ℕ × List (ℕ × ℕ)
  have hf : Computable (fun z : A => z.1) := Computable.fst
  have hg : Computable (fun z : A => z.2.2) := Computable.snd.comp Computable.snd
  exact computable_foldl hf hg computable_boundStep.to₂

lemma computable_bound : Computable₂ bound := by
  exact ((Primrec.list_getD (0,0)).to_comp.comp
    (computable_boundFrom.comp (Computable.fst.pair (Computable.snd.pair (Computable.const []))))
    (Computable.const 0))

lemma computable_approximation (d : ℕ) [NeZero d] : Computable
    (fun z : NumericProgram × ℕ × (Fin d → ℚ) × ℕ =>
      approximation z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have herr : Computable (fun z : NumericProgram × ℕ × (Fin d → ℚ) × ℕ => (z.1.bound z.2.1).2) := Computable.snd.comp (computable_bound.comp Computable.fst (Computable.fst.comp Computable.snd))
  exact (Primrec.list_getD (0 : ℚ)).to_comp.comp
    ((computable_rationalFrom d).comp (Computable.fst.pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Primrec.nat_add.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)) herr).pair
          (Computable.const []))))) (Computable.const 0)

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericDifferentiation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_drop (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (q : List ℝ) :
    ((o.dual d k).realFrom x q).drop 5 = q := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, tag]

lemma dual_value (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 4 0 = o.real d x s := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp [dual, dualCase, NumericProgram.realFrom, real, tag, rat, left, right, h]

lemma dual_differential (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) :
    ((o.dual d k).realFrom x q).getD 0 0 =
      o.differential d k (fun a => s.getD a 0) (fun a => q.getD (5*a) 0) := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.realFrom, real, differential, tag, rat, left, right,
      Nat.add_assoc, h, pow_two]
  change (((if Fin.ofNat d a = k then 1 else 0) : ℚ) : ℝ) =
    (if Fin.ofNat d a = k then 1 else 0)
  by_cases hh : Fin.ofNat d a = k <;>
    simp only [hh, ite_true, ite_false, Rat.cast_one, Rat.cast_zero]

lemma dual_valid (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s q : List ℝ)
    (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : o.Valid s) :
    (o.dual d k).ValidFrom x q := by
  simp only [List.getD] at h
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ValidFrom, Valid, real, tag, rat, left, right, h] at hv ⊢
  exact hv

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericScopes ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericJets ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma dual_register (k : Fin d) (o : NumericOp) (x : Fin d → ℝ) (s : List ℝ) (a : ℕ) :
    ((o.dual d k).realFrom x s).getD (5+a) 0 = s.getD a 0 := by
  have h := congrArg (fun l : List ℝ => l.getD a 0) (o.dual_drop d k x s)
  simpa [List.getD, List.getElem?_drop] using h

lemma dual_length (k : Fin d) (o : NumericOp) : (o.dual d k).length = 5 := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> rfl

lemma dual_scoped (k : Fin d) (o : NumericOp) {n : ℕ} (h : o.Scoped n) :
    (o.dual d k).ScopedFrom (5*n) := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;>
    simp [dual, dualCase, NumericProgram.ScopedFrom, Scoped, tag, left, right] at h ⊢
  all_goals omega

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma jetStep_length (k : Fin d) (p : NumericProgram) : (p.jetStep k).length = 5*p.length := by
  induction p with
  | nil => rfl
  | cons o p ih => simp only [jetStep, List.flatMap_cons, List.length_append,
      NumericOp.dual_length, List.length_cons] at ih ⊢; omega

lemma jetStep_scoped (k : Fin d) (p : NumericProgram) {n : ℕ} (h : p.ScopedFrom n) :
    (p.jetStep k).ScopedFrom (5*n) := by
  induction p generalizing n with
  | nil => trivial
  | cons o p ih =>
    rw [jetStep, List.flatMap_cons, scopedFrom_concat, NumericOp.dual_length]
    exact ⟨o.dual_scoped d k h.1, by simpa [jetStep, Nat.mul_add] using ih h.2⟩

lemma jetStep_closed (k : Fin d) (p : NumericProgram) (h : p.Closed) :
    (p.jetStep k).Closed := p.jetStep_scoped k h

lemma jetStep_validFrom (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ)
    (s q : List ℝ) (h : ∀ a, q.getD (5*a+4) 0 = s.getD a 0) (hv : p.ValidFrom x s) :
    (p.jetStep k).ValidFrom x q ∧
      ∀ a, ((p.jetStep k).realFrom x q).getD (5*a+4) 0 = (p.realFrom x s).getD a 0 := by
  induction p generalizing s q with
  | nil => exact ⟨trivial, h⟩
  | cons o p ih =>
    have ho := o.dual_valid d k x s q h hv.1
    have hh (a : ℕ) : ((o.dual d k).realFrom x q).getD (5*a+4) 0 =
        (o.real d x s :: s).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k x s q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5,
          List.getD_cons_succ] using (o.dual_register d k x q (5*a+4)).trans (h a)
    have hi := ih _ _ hh hv.2
    refine ⟨?_, ?_⟩
    · exact (validFrom_concat _ _ x q).mpr ⟨ho, hi.1⟩
    · simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
        List.foldl_cons, List.foldl_append] using hi.2

lemma jetStep_valid (k : Fin d) (p : NumericProgram) {x : Fin d → ℝ} (hv : p.Valid x) :
    (p.jetStep k).Valid x := (p.jetStep_validFrom k x [] [] (by simp) hv).1

lemma jetStep_hasDerivAtFrom (k : Fin d) (p : NumericProgram)
    (x : ℝ → Fin d → ℝ) (s : ℝ → List ℝ) (q : List ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (h : ∀ a, q.getD (5*a+4) 0 = (s t).getD a 0)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (q.getD (5*a) 0) t)
    (hv : p.ValidFrom (x t) (s t)) :
    ∀ a, HasDerivAt (fun t => (p.realFrom (x t) (s t)).getD a 0)
      (((p.jetStep k).realFrom (x t) q).getD (5*a) 0) t := by
  induction p generalizing s q with
  | nil => exact hs
  | cons o p ih =>
    let s' : ℝ → List ℝ := fun v => o.real d (x v) (s v) :: s v
    let q' : List ℝ := (o.dual d k).realFrom (x t) q
    have hh (a : ℕ) : q'.getD (5*a+4) 0 = (s' t).getD a 0 := by
      cases a with
      | zero => exact o.dual_value d k (x t) (s t) q h
      | succ a =>
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 5, s', q',
          List.getD_cons_succ] using (o.dual_register d k (x t) q (5*a+4)).trans (h a)
    have hd (a : ℕ) : HasDerivAt (fun v => (s' v).getD a 0) (q'.getD (5*a) 0) t := by
      cases a with
      | zero =>
        change HasDerivAt (fun v => o.real d (x v) (s v))
          (((o.dual d k).realFrom (x t) q).getD 0 0) t
        rw [o.dual_differential d k (x t) (s t) q h]
        exact o.hasDerivAt d k x s _ t hx hs hv.1
      | succ a =>
        change HasDerivAt (fun v => (s v).getD a 0)
          (((o.dual d k).realFrom (x t) q).getD (5*(a+1)) 0) t
        rw [show 5*(a+1)=5+5*a by omega, o.dual_register d k]
        exact hs a
    have hi := ih s' q' hh hd hv.2
    simpa only [jetStep, List.flatMap_cons, realFrom_concat, realFrom,
      List.foldl_cons, List.foldl_append, s', q'] using hi

lemma differentiableAtFrom (p : NumericProgram) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : p.ValidFrom x (s x)) :
    ∀ a, DifferentiableAt ℝ (fun y => (p.realFrom y (s y)).getD a 0) x := by
  induction p generalizing s with
  | nil => exact hs
  | cons o p ih =>
    apply ih (fun y => o.real d y (s y) :: s y) ?_ hv.2
    intro a
    cases a with
    | zero => exact o.differentiableAt d x s hs hv.1
    | succ a => exact hs a

lemma differentiableAt (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    DifferentiableAt ℝ p.real x :=
  p.differentiableAtFrom x (fun _ => []) (fun _ => differentiableAt_const _) hv 0

lemma jetStep_real (k : Fin d) (p : NumericProgram) (x : Fin d → ℝ) (hv : p.Valid x) :
    (p.jetStep k).real x = fderiv ℝ p.real x (Pi.single k 1) := by
  let y : ℝ → Fin d → ℝ := fun t => x + t • Pi.single k 1
  have hy (i : Fin d) : HasDerivAt (fun t => y t i) (if i=k then 1 else 0) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (x i)).add ((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single k (1:ℝ) : Fin d → ℝ) i))
    simpa only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Function.const_apply, Pi.mul_apply, id_eq, mul_ite, mul_one, mul_zero, eq_comm, Pi.add_def, zero_add] using h
  have he : y 0 = x := by simp [y]
  have hh := p.jetStep_hasDerivAtFrom k y (fun _ => []) [] 0 hy (by simp)
    (by intro a; simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by change p.Valid (y 0); rw [he]; exact hv) 0
  have hf := (p.differentiableAt x hv).hasFDerivAt.hasLineDerivAt (Pi.single k 1)
  exact HasDerivAt.unique (by simpa only [real, he, Nat.mul_zero] using hh) hf

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericAlgebra ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma computable_dual : Computable (fun z : Fin d × NumericOp => z.2.dual d z.1) := by
  have hi : Computable (fun a : ℕ => Fin.ofNat d a) :=
    (Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const d))).to_comp
  have he : Computable (fun z : Fin d × NumericOp => decide (Fin.ofNat d z.2.left = z.1)) :=
    Primrec.eq.decide.to_comp.comp (hi.comp (by unfold left; fun_prop)) Computable.fst
  have hb : Computable (fun z : Fin d × NumericOp =>
      if Fin.ofNat d z.2.left = z.1 then (1:ℚ) else 0) :=
    computable_ite he (Computable.const 1) (Computable.const 0)
  have hc (j : Fin 9) : Computable (fun z : Fin d × NumericOp =>
      dualCase d z.1 j z.2) := by
    fin_cases j <;> dsimp only [dualCase, left, right] <;> fun_prop
  exact computable_fin_cases (i := fun z => z.2.tag) (by unfold tag; fun_prop) hc

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

lemma computable_jetStep : Computable (fun z : Fin d × NumericProgram => z.2.jetStep z.1) := by
  unfold jetStep
  have hd : Computable (fun z : (Fin d × NumericProgram) × NumericOp => z.2.dual d z.1.1) :=
    Computable.comp (f := fun z : Fin d × NumericOp => z.2.dual d z.1)
      (g := fun z : (Fin d × NumericProgram) × NumericOp => (z.1.1,z.2))
      (NumericOp.computable_dual d) (by fun_prop)
  exact ComputableRules.flatMapList (f := fun z : Fin d × NumericProgram => z.2)
    (g := fun z o => o.dual d z.1) Computable.snd
    hd

end BalancedTransport.Effectivity.NumericProgram
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Elementary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e] {f g : (Fin d → ℝ) → ℝ}

lemma differentiable (hf : Elementary f) : Differentiable ℝ f := by
  obtain ⟨p, _, _, hv, rfl⟩ := hf
  exact fun x => p.differentiableAt x (hv x)

lemma coordinateDerivative (hf : Elementary f) (k : Fin d) :
    Elementary (fun x => fderiv ℝ f x (Pi.single k 1)) := by
  obtain ⟨p, hn, hc, hv, rfl⟩ := hf
  refine ⟨p.jetStep k, ?_, p.jetStep_closed k hc, fun x => p.jetStep_valid k (hv x), ?_⟩
  · apply List.length_pos_iff.mp
    rw [NumericProgram.jetStep_length]
    exact Nat.mul_pos (by decide) (List.length_pos_iff.mpr hn)
  · funext x
    exact p.jetStep_real k x (hv x)

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
variable {d e : ℕ} [NeZero d] [NeZero e]

end BalancedTransport.Effectivity.Elementary
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryCalculus ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.Elementary
open BalancedTransport.Geometry

lemma congr {d : ℕ} [NeZero d] {f g : (Fin d → ℝ) → ℝ} (hf : Elementary f) (he : ∀x, f x = g x) : Elementary g := by
  rwa [← funext he]

end BalancedTransport.Effectivity.Elementary
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryCurve
open BalancedTransport.Geometry

end BalancedTransport.Effectivity.ElementaryCurve
end

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry

lemma fieldArgs_space_hasFDerivAt {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) :
    HasFDerivAt (fun y => fieldArgs p t y)
      (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
        Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
          (fun _ => 0) k)) x := by
  apply hasFDerivAt_pi.mpr
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa [fieldArgs] using hasFDerivAt_const t x
    · simpa [fieldArgs] using hasFDerivAt_apply i x
  · intro j
    simpa [fieldArgs] using hasFDerivAt_const (p j) x

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.ElementaryScalar
open BalancedTransport.Geometry
variable {d : ℕ} {f g : (Fin d → ℝ) → Field ℝ}

lemma fullTimeD (h : ElementaryScalar f) : ElementaryScalar (fun p => Geometry.fullTimeD (f p)) := by
  have hd := h.coordinateDerivative (Fin.castAdd d 0)
  apply hd.congr
  intro z
  have hh := (h.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD] using he.deriv.symm

end BalancedTransport.Effectivity.ElementaryScalar
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ElementaryJets ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open _root_.OAI.BalancedTransport.Geometry

lemma ElementaryScalar.scalarMixedD {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (a : MultiIndex) :
    ElementaryScalar (fun p => scalarMixedD a (f p)) := by
  induction a with
  | nil => exact hf
  | cons i a ih => cases i with
    | none => exact ih.fullTimeD
    | some i => exact ih.spaceD i

lemma coordinateDerivative_field_time {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (z : Fin (4+d) → ℝ) :
    fderiv ℝ (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z)) z
      (Pi.single (fieldCoordinate d none) 1) =
        fullTimeD (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  have hh := (hf.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp_hasDerivAt (fieldTime z) (fieldArgs_time_hasDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,Geometry.fullTimeD,
    fieldCoordinate] using he.deriv.symm

lemma fieldArgs_space_single {d : ℕ} (i : Fin 3) :
    (ContinuousLinearMap.pi (fun k : Fin (4+d) =>
      Fin.addCases (Fin.cases (0 : Space →L[ℝ] ℝ) (fun i => ContinuousLinearMap.proj i))
        (fun _ => 0) k) : Space →L[ℝ] (Fin (4+d) → ℝ)) (Pi.single i 1) =
      Pi.single (fieldCoordinate d (some i)) 1 := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · have hn : Fin.castAdd d (0 : Fin 4) ≠ Fin.castAdd d i.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_succ, Fin.val_zero] at this; omega
      simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_zero,
        zero_apply, Pi.single_apply, ite_eq_right hn,fieldCoordinate]
    · simp only [ContinuousLinearMap.pi_apply, Fin.addCases_left, Fin.cases_succ,
        ContinuousLinearMap.proj_apply, Pi.single_apply, Fin.castAdd_inj, Fin.succ_inj,fieldCoordinate]
  · intro j
    have hn : Fin.natAdd 4 j ≠ Fin.castAdd d i.succ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this; omega
    simp only [ContinuousLinearMap.pi_apply, Fin.addCases_right,
      zero_apply, Pi.single_apply, ite_eq_right hn,fieldCoordinate]

lemma coordinateDerivative_field_space {d : ℕ} {f : (Fin d → ℝ) → Field ℝ}
    (hf : ElementaryScalar f) (z : Fin (4+d) → ℝ) (i : Fin 3) :
    fderiv ℝ (fun z => f (fieldParam z) (fieldTime z) (fieldSpace z)) z
      (Pi.single (fieldCoordinate d (some i)) 1) =
        spaceD i (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  have hh := (hf.differentiable (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z))).hasFDerivAt
  have he := hh.comp (fieldSpace z) (fieldArgs_space_hasFDerivAt (fieldParam z) (fieldTime z) (fieldSpace z))
  simpa only [Function.comp_def, fieldArgs_parts,fieldParam_args,fieldTime_args,fieldSpace_args,spaceD,
    ContinuousLinearMap.comp_apply, fieldArgs_space_single] using congrArg (fun l => l (Pi.single i 1)) he.fderiv.symm

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
open _root_.OAI.BalancedTransport.Geometry

lemma fieldJet_fold (d : ℕ) (a : MultiIndex) (p : NumericProgram) :
    fieldJet d a p = a.reverse.foldl (fun q i => q.jetStep (fieldCoordinate d i)) p := by
  induction a with
  | nil => rfl
  | cons i a ih => simp [fieldJet, ih]

lemma computable_fieldCoordinate (d : ℕ) : Computable (fieldCoordinate d) := by
  have h : Primrec (fun i : Option (Fin 3) => (Option.casesOn i 0 (fun j => j.val+1) : ℕ)) :=
    Primrec.option_casesOn Primrec.id (Primrec.const 0)
      (Primrec.succ.comp (Primrec.fin_val.comp Primrec.snd)).to₂
  have hv : Primrec (fun i : Option (Fin 3) => (fieldCoordinate d i).val) :=
    h.of_eq (fun i => by cases i <;> rfl)
  exact (Primrec.fin_val_iff.mp hv).to_comp

lemma computable_fieldJet_step (d : ℕ) :
    Computable (fun z : (MultiIndex × NumericProgram) × (NumericProgram × Option (Fin 3)) =>
      jetStep (fieldCoordinate d z.2.2) z.2.1) := by
  let A := (MultiIndex × NumericProgram) × (NumericProgram × Option (Fin 3))
  have hk : Computable (fun z : A => fieldCoordinate d z.2.2) :=
    (computable_fieldCoordinate d).comp (Computable.snd.comp Computable.snd)
  have hp : Computable (fun z : A => z.2.1) := Computable.fst.comp Computable.snd
  exact Computable.comp
    (f := fun z : Fin (4+d) × NumericProgram => jetStep z.1 z.2)
    (g := fun z : A => (fieldCoordinate d z.2.2, z.2.1))
    (computable_jetStep (d := 4+d)) (hk.pair hp)

lemma computable_fieldJet (d : ℕ) :
    Computable (fun z : MultiIndex × NumericProgram => fieldJet d z.1 z.2) := by
  have hl : Computable (fun z : MultiIndex × NumericProgram => z.1.reverse) :=
    Primrec.list_reverse.to_comp.comp Computable.fst
  have h := computable_foldl hl Computable.snd (computable_fieldJet_step d).to₂
  exact h.of_eq (fun z => (fieldJet_fold d z.1 z.2).symm)

lemma fieldJet_valid (d : ℕ) (a : MultiIndex) (p : NumericProgram) (z : Fin (4+d) → ℝ)
    (hp : p.Valid z) : (fieldJet d a p).Valid z := by
  induction a with
  | nil => exact hp
  | cons i a ih => exact jetStep_valid _ _ ih

lemma fieldJet_real {d : ℕ} {f : (Fin d → ℝ) → Field ℝ} (hf : ElementaryScalar f)
    (p : NumericProgram) (hp : ∀ z : Fin (4+d) → ℝ, p.Valid z)
    (he : ∀z, p.real z = f (fieldParam z) (fieldTime z) (fieldSpace z)) (a : MultiIndex) :
    ∀ z : Fin (4+d) → ℝ, (fieldJet d a p).real z =
      scalarMixedD a (f (fieldParam z)) (fieldTime z) (fieldSpace z) := by
  induction a with
  | nil => exact he
  | cons i a ih =>
    intro z
    rw [fieldJet, jetStep_real _ _ _ (fieldJet_valid d a p z (hp z)), funext ih]
    cases i with
    | none => exact coordinateDerivative_field_time (hf.scalarMixedD a) z
    | some i => exact coordinateDerivative_field_space (hf.scalarMixedD a) z i

end BalancedTransport.Effectivity.NumericProgram
end

noncomputable section
namespace BalancedTransport.Effectivity
open _root_.OAI.BalancedTransport.Geometry

lemma scalarMixedD_component {v : Velocity} (hv : JointSmooth v) (a : MultiIndex) (i : Fin 3) :
    scalarMixedD a (fun t x => v t x i) = fun t x => fullMixedD a v t x i := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    cases j with
    | none =>
      simp only [scalarMixedD, ih, fullMixedD, fullTimeD]
      ext t x
      exact ((hasDerivAt_pi.mp
        (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t).hasDerivAt) i).deriv
    | some j =>
      simp only [scalarMixedD, ih, fullMixedD, spaceD]
      ext t x
      have he := (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x
        (((hv.fullMixedD a).slice t).differentiable (by simp) x).hasFDerivAt
      exact congrArg (fun l => l (Pi.single j 1)) he.fderiv

theorem elementary_jet_programs {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀p, JointSmooth (v p)) :
    ∃ ps : Fin 3 → NumericProgram,
      ∀ i a z, (NumericProgram.fieldJet d a (ps i)).Valid (fieldArgs (fieldParam z) (fieldTime z) (fieldSpace z)) ∧
        (NumericProgram.fieldJet d a (ps i)).real z =
          fullMixedD a (v (fieldParam z)) (fieldTime z) (fieldSpace z) i := by
  choose ps hne hclosed hp he using (fun i => hv i)
  refine ⟨ps, ?_⟩
  intro i a z
  refine ⟨NumericProgram.fieldJet_valid d a (ps i) _ (hp i _), ?_⟩
  rw [NumericProgram.fieldJet_real (hv i) (ps i) (hp i) (fun z => congrFun (he i) z)]
  exact congrFun (congrFun (scalarMixedD_component (hs (fieldParam z)) a i) (fieldTime z)) (fieldSpace z)

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EffectiveGluing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

lemma computable_fin_lam {α β : Type*} [Primcodable α] [Primcodable β]
    {n : ℕ} {f : α → Fin n → β} (hf : ∀ i, Computable (fun a => f a i)) :
    Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun a => by funext i; simp)

lemma fieldRationalArgs_cast {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) :
    (fun i => (fieldRationalArgs p t x i : ℝ)) = fieldArgs (fun i => (p i : ℝ)) t (rationalSpace x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j <;> simp [fieldRationalArgs, fieldArgs, rationalSpace]
  · simp [fieldRationalArgs, fieldArgs]

lemma computable_fieldRationalArgs (d : ℕ) :
    Computable (fun z : (Fin d → ℚ) × RationalPoint => fieldRationalArgs z.1 z.2.1 z.2.2) := by
  apply computable_fin_lam
  intro i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [id_eq,fieldRationalArgs,Fin.addCases_left,Fin.cases_zero] using
        (Computable.fst.comp Computable.snd : Computable (fun z : (Fin d → ℚ) × RationalPoint => z.2.1))
    · simpa only [id_eq,fieldRationalArgs,Fin.addCases_left,Fin.cases_succ] using
        (Computable.fin_app.comp (Computable.snd.comp Computable.snd) (Computable.const l) :
          Computable (fun z : (Fin d → ℚ) × RationalPoint => z.2.2 l))
  · simpa only [id_eq,fieldRationalArgs,Fin.addCases_right] using
      (Computable.fin_app.comp Computable.fst (Computable.const k) :
        Computable (fun z : (Fin d → ℚ) × RationalPoint => z.1 k))

lemma fieldArgs_bound {d : ℕ} (p : Fin d → ℝ) (t : ℝ) (x : Space) (C S : ℕ)
    (hp : ∀ i, |p i| ≤ C) (ht : |t| ≤ 1) (hx : ∀ i, |x i| ≤ S) :
    ∀ j, |fieldArgs p t x j| ≤ (C+1+S : ℕ) := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · refine Fin.cases ?_ (fun i => ?_) k
    · change |t| ≤ _; push_cast; linarith [Nat.cast_nonneg C (α := ℝ), Nat.cast_nonneg S (α := ℝ)]
    · simp only [fieldArgs,Fin.append_left,Fin.cons_succ]; push_cast; linarith [hx i, Nat.cast_nonneg C (α := ℝ)]
  · simp only [fieldArgs,Fin.append_right]; push_cast; linarith [hp k, Nat.cast_nonneg S (α := ℝ)]

lemma computable_sum_nat {α ι : Type*} [Primcodable α] (s : Finset ι)
    {f : ι → α → ℕ} (hf : ∀ i ∈ s, Computable (f i)) :
    Computable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Computable.const (0 : ℕ) : Computable (fun _ : α => 0))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      Primrec.nat_add.to_comp.comp (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma computable_gridRadius (C : ℕ) : Computable (gridRadius C) := by
  apply Primrec.nat_add.to_comp.comp (Computable.const (C+1))
  apply computable_sum_nat
  intro i _
  exact primrec_int_natAbs.to_comp.comp (computable_rat_num.comp
    (Computable.fin_app.comp Computable.id (Computable.const i)))

lemma gridRadius_bound {d : ℕ} (p : Fin d → ℚ) (t : ℚ) (x : Fin 3 → ℚ) (C : ℕ)
    (hp : ∀ i, |(p i : ℝ)| ≤ C) (ht : |(t : ℝ)| ≤ 1) :
    ∀ j, |(fieldRationalArgs p t x j : ℝ)| ≤ gridRadius C x := by
  intro j
  rw [congrFun (fieldRationalArgs_cast p t x) j]
  apply fieldArgs_bound _ _ _ C _ hp ht _ j
  intro i
  exact (rat_abs_le_num (x i)).trans (by exact_mod_cast
    (Finset.single_le_sum (fun j _ => Nat.zero_le ((x j).num.natAbs)) (Finset.mem_univ i)))

theorem elementary_jet_evaluators {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀ p, JointSmooth (v p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C : ℕ)
    (hC : ∀ n i, |(κ n i : ℝ)| ≤ C) :
    ∃ E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ,
    ∃ b : MultiIndex × ℕ → ℕ,
      Computable E ∧ Computable b ∧
      (∀ m a z n, |(z.1 : ℝ)| ≤ 1 → ∀ i,
        |(E (m,a,z,n) i : ℝ) - fullMixedD a (v (fun j => (κ m j : ℝ)))
          z.1 (rationalSpace z.2) i| ≤ error n) ∧
      (∀ m a t x (S : ℕ), |t| ≤ 1 → ‖x‖ ≤ (S : ℝ) →
        ‖fullMixedD a (v (fun j => (κ m j : ℝ))) t x‖ ≤ (b (a,S) : ℝ)) := by
  obtain ⟨ps,hps⟩ := elementary_jet_programs hv hs
  let E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ := fun z i =>
    (NumericProgram.fieldJet d z.2.1 (ps i)).approximation (gridRadius C z.2.2.1.2)
      (fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2) z.2.2.2
  let b : MultiIndex × ℕ → ℕ := fun z =>
    ∑ i, ((NumericProgram.fieldJet d z.1 (ps i)).bound (C+1+z.2)).1
  have hE : Computable E := by
    apply computable_fin_lam
    intro i
    let A := ℕ × MultiIndex × RationalPoint × ℕ
    have hp : Computable (fun z : A => NumericProgram.fieldJet d z.2.1 (ps i)) :=
      (NumericProgram.computable_fieldJet d).comp
        ((Computable.fst.comp Computable.snd).pair (Computable.const (ps i)))
    have hc : Computable (fun z : A => gridRadius C z.2.2.1.2) :=
      (computable_gridRadius C).comp (Computable.snd.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hx : Computable (fun z : A => fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2) :=
      Computable.comp (f := fun z : (Fin d → ℚ) × RationalPoint => fieldRationalArgs z.1 z.2.1 z.2.2)
        (g := fun z : A => (κ z.1,z.2.2.1)) (computable_fieldRationalArgs d)
        ((hκ.comp Computable.fst).pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    have hn : Computable (fun z : A => z.2.2.2) :=
      Computable.snd.comp (Computable.snd.comp Computable.snd)
    exact Computable.comp
      (f := fun z : NumericProgram × ℕ × (Fin (4+d) → ℚ) × ℕ =>
        z.1.approximation z.2.1 z.2.2.1 z.2.2.2)
      (g := fun z : A => (NumericProgram.fieldJet d z.2.1 (ps i), gridRadius C z.2.2.1.2,
        fieldRationalArgs (κ z.1) z.2.2.1.1 z.2.2.1.2, z.2.2.2))
      (NumericProgram.computable_approximation (4+d)) (hp.pair (hc.pair (hx.pair hn)))
  have hb : Computable b := by
    apply computable_sum_nat
    intro i _
    have hp : Computable (fun z : MultiIndex × ℕ => NumericProgram.fieldJet d z.1 (ps i)) :=
      (NumericProgram.computable_fieldJet d).comp
        (Computable.fst.pair (Computable.const (ps i)))
    have hc : Computable (fun z : MultiIndex × ℕ => C+1+z.2) :=
      Primrec.nat_add.to_comp.comp (Computable.const (C+1)) Computable.snd
    exact Computable.fst.comp (NumericProgram.computable_bound.comp hp hc)
  refine ⟨E,b,hE,hb,?_,?_⟩
  · intro m a z n ht i
    have hh := hps i a (fieldArgs (fun j => (κ m j : ℝ)) z.1 (rationalSpace z.2))
    simp only [fieldParam_args,fieldTime_args,fieldSpace_args] at hh
    have he := (NumericProgram.fieldJet d a (ps i)).approximation_spec (gridRadius C z.2)
      (fieldRationalArgs (κ m) z.1 z.2) n (gridRadius_bound _ _ _ C (hC m) ht)
      (by rw [fieldRationalArgs_cast]; exact hh.1)
    rw [fieldRationalArgs_cast, hh.2] at he
    exact he
  · intro m a t x S ht hx
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg (b (a,S)))).mpr
    intro i
    rw [Real.norm_eq_abs]
    have hh := hps i a (fieldArgs (fun j => (κ m j : ℝ)) t x)
    simp only [fieldParam_args,fieldTime_args,fieldSpace_args] at hh
    have hi : ∀ i, |x i| ≤ S := fun i =>
      (le_trans (norm_le_pi_norm x i) hx)
    have he := (NumericProgram.fieldJet d a (ps i)).magnitude (C+1+S)
      (fieldArgs (fun j => (κ m j : ℝ)) t x)
      (fieldArgs_bound _ _ _ C S (hC m) ht hi) hh.1
    rw [hh.2] at he
    exact he.trans (by exact_mod_cast
      (Finset.single_le_sum (fun j _ => Nat.zero_le
        ((NumericProgram.fieldJet d a (ps j)).bound (C+1+S)).1) (Finset.mem_univ i)))

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.elementary_jet_evaluators := @_root_.OAI.BalancedTransport.Effectivity.elementary_jet_evaluators

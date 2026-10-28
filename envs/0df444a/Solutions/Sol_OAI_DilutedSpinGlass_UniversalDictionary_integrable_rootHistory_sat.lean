-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:40:15.520986+00:00
-- url     : https://prove2.me/submissions/efeb9e76-4557-4c36-bd68-95506bc62374

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_rootHistory_polarization_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type}

theorem leafSum_eq_sum {n : ℕ} (S : PrescribedTree n)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω S) :
    leafSum S f x = ∑ a : Leaf S, f (pathAt S a x) := by
  induction S with
  | leaf =>
    change f () = ∑ _ : Unit, f ()
    simp
  | @node n k C ih =>
    change (∑ i, leafSum (C i) (fun y => f ((x i).1,y)) (x i).2) = _
    have hL : (∑ a : Leaf (.node k C), f (pathAt (.node k C) a x)) =
        ∑ i, ∑ a : Leaf (C i), f ((x i).1,pathAt (C i) a (x i).2) := Fintype.sum_sigma _
    rw [hL]
    exact Finset.sum_congr rfl (fun i _ => ih i _ _)

theorem leafSum_single (n : ℕ) (f : FinitePath Ω n → ℝ) (x : Sample Ω (single n)) :
    leafSum (single n) f x = f (singlePath n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ i : Fin 1, leafSum (single n) (fun y => f ((x i).1,y)) (x i).2) = _
    rw [Fintype.sum_subsingleton]
    exact ih _ _

private theorem leafSum_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (f : FinitePath Ω (n+1) → ℝ) (x : Ω × Sample Ω S') :
    leafSum S' (fun y => f (x.1,y)) x.2 =
    leafSum S (fun y => f ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,y))
      (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2 := by
  subst S'
  rfl

/-- Exactly one terminal mark is added by growth, and its ancestry is the
new path, not a path chosen by equality of sample values. -/
theorem leafSum_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω (grow S v)) :
    leafSum (grow S v) f x = leafSum S f (oldSample S v x) + f (newPath S v x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (∑ j : Fin (k+1), leafSum (Fin.cases (single n) C j)
        (fun y => f ((x j).1,y)) (x j).2) = _
      erw [Fin.sum_univ_succ]
      have hh := leafSum_single n (fun y => f ((x 0).1,y)) (x 0).2
      calc
        _ = f ((x 0).1,singlePath n (x 0).2) +
            ∑ i : Fin k, leafSum (C i) (fun y => f ((x i.succ).1,y)) (x i.succ).2 :=
          congrArg₂ (· + ·) hh rfl
        _ = _ := add_comm _ _
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      have hp (j : Fin k) :
          leafSum (C' j) (fun y => f ((x j).1,y)) (x j).2 =
          leafSum (C j) (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 +
              if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 0 := by
        by_cases hj : j = i
        · subst j
          have hcast := leafSum_cast (grow (C i) v) (C' i)
            (Function.update_self ..) f (x i)
          let y : Ω × Sample Ω (grow (C i) v) :=
            cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
          have hh := ih i v (fun z => f (y.1,z)) y.2
          have he : leafSum (C' i) (fun z => f ((x i).1,z)) (x i).2 =
              leafSum (C i) (fun z => f (y.1,z)) (oldSample (C i) v y.2) +
                f (y.1,newPath (C i) v y.2) := hcast.trans hh
          erw [oldSample.eq_1, newPath.eq_1]
          dsimp only [id]
          simp only [dite_true, ite_true]
          exact he
        · have hc := leafSum_cast (C j) (C' j) (Function.update_of_ne hj ..) f (x j)
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hj, ite_eq_right hj, add_zero]
          exact hc
      change (∑ j, leafSum (C' j) (fun y => f ((x j).1,y)) (x j).2) = _
      calc
        _ = ∑ j, (leafSum (C j)
            (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 +
            if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 0) :=
          Finset.sum_congr rfl (fun j _ => hp j)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]; rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

/-- The exact signed budget for internal extensions with finite exponent indices. -/
theorem sum_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ) :
    (∑ v : Internal S, gamma S m v) = m 0 - (leaves S : ℝ) * m (Fin.last n) := by
  induction S with
  | leaf =>
    change (∑ v : Empty, gamma .leaf m v) = _
    have hs : (∑ v : Empty, gamma .leaf m v) = 0 :=
      Finset.sum_eq_zero (fun v _ => nomatch v)
    rw [hs]
    simp [leaves, Fin.last_zero]
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    erw [Fintype.sum_option, Fintype.sum_sigma]
    change m 0 - (k : ℝ) * m 1 +
      (∑ i, ∑ v : Internal (C i), gamma (C i) (fun j => m j.succ) v) = _
    simp_rw [ih]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin, leaves, Nat.cast_sum, Fin.succ_last, Fin.succ_zero_eq_one]
    rw [← Finset.sum_mul]
    ring

theorem gamma_nonpos {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (v : Internal S) : gamma S m v ≤ 0 := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change m 0 - (k : ℝ) * m 1 ≤ 0
      have hh : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.property
      have h01 := hm (show (0 : Fin (n+2)) ≤ 1 by exact Fin.zero_le _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hh) (hpos 1)]
    | some v =>
      obtain ⟨i,v⟩ := v
      exact ih i (fun j => m j.succ) (fun a b h => hm (Fin.succ_le_succ_iff.mpr h))
        (fun j => hpos j.succ) v

/-- Absolute coefficients sum to the number of old leaves. -/
theorem sum_abs_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) :
    (∑ v : Internal S, |gamma S m v|) = (leaves S : ℝ) := by
  simp_rw [abs_of_nonpos (gamma_nonpos S m hm hpos _)]
  rw [Finset.sum_neg_distrib, sum_gamma, hroot, hend]
  ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem leafSum_const {Ω : Type} {n : ℕ} (S : PrescribedTree n)
    (c : ℝ) (x : Sample Ω S) : leafSum S (fun _ => c) x = (leaves S : ℝ) * c := by
  induction S with
  | leaf => simp [leafSum, leaves]
  | @node n k C ih =>
    change (∑ i, leafSum (C i) (fun _ => c) (x i).2) = _
    simp_rw [ih]
    simp only [leaves, Nat.cast_sum, Finset.sum_mul]

theorem leaves_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S) :
    leaves (grow S v) = leaves S + 1 := by
  have hh := @leafSum_grow Unit n S v (fun _ => 1) (trivialSample (grow S v))
  simp only [leafSum_const, mul_one] at hh
  exact_mod_cast hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProductTowers
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

theorem tilt_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).tilt m (fun z => f z.1) =
      (P.tilt m f).bind (fun _ => Q) := by
  ext z
  change P.weight z.1 * Q.weight z.2 * Real.exp (m*f z.1) /
      (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) =
      (P.weight z.1 * Real.exp (m*f z.1) / P.expMoment m f) * Q.weight z.2
  have hh : (P.bind (fun _ => Q)).expMoment m (fun z => f z.1) = P.expMoment m f := by
    simp [expMoment]
  rw [hh]
  ring
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

theorem tilt_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    tilt n (prod n T U) m (fun y => f (pathFst n y)) = prod n (tilt n T m f) U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext
    · change (T.1.bind (fun _ => U.1)).tilt (m 0)
        (fun z => backwardLog n (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1,pathFst n y))) =
        (T.1.tilt (m 0) (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
          (fun y => f (x,y)))).bind (fun _ => U.1)
      have hh : (fun z : Ω × Λ => backwardLog n
          (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
          (fun y => f (z.1, pathFst n y))) =
          (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
            (fun y => f (z.1,y))) := by
        funext z
        exact backwardLog_prod_fst n (T.2 z.1) (U.2 z.2) (fun j => m j.succ)
          (fun y => f (z.1,y))
      rw [hh]
      exact FiniteLaw.tilt_bind_fst T.1 U.1 (m 0)
        (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
    · funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem leafSum_mono {n : ℕ} (S : PrescribedTree n) {f g : FinitePath Ω n → ℝ}
    (h : ∀ y, f y ≤ g y) (x : Sample Ω S) : leafSum S f x ≤ leafSum S g x := by
  simp only [leafSum_eq_sum]
  exact Finset.sum_le_sum (fun a _ => h _)

theorem fullyProtected_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) (G : Sample Ω S → ℝ) :
    fullyProtected S T m D G 0 = (sampleLaw S T).expect G := by
  simp [fullyProtected, KernelTower.tilt_const n T _ hm, leafSum_const]

theorem anchorEval_zero {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (D : FinitePath Ω n → ℝ) {ι : Type} (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ) :
    anchorEval S T m D A U G 0 = (sampleLaw S T).expect G := by
  simp [anchorEval, fullyProtected_zero S T m hm]

omit [Fintype Ω] in
/-- The denominator in the protected tree rule is uniformly bounded on a
fixed real neighborhood of zero, independently of all kernels and depth. -/
theorem protected_density_bound {n : ℕ} (S : PrescribedTree n)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {t : ℝ} (ht : |t| ≤ 1/2) (x : Sample Ω S) :
    Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x) ≤ (2:ℝ) ^ leaves S := by
  have hlow (y : FinitePath Ω n) : (1:ℝ)/2 ≤ 1+t*D y := by
    have ha : |t * D y| ≤ 1/2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hD y) (abs_nonneg t)).trans (by simpa using ht)
    have := (abs_le.mp ha).1
    linarith
  have hh := leafSum_mono S (f := fun _ => -Real.log 2)
    (g := fun y => Real.log (1+t*D y)) (fun y => by
      have h := Real.strictMonoOn_log.monotoneOn (show (1:ℝ)/2 ∈ Set.Ioi 0 by norm_num)
        (show 1+t*D y ∈ Set.Ioi 0 by change 0 < 1+t*D y; linarith [hlow y]) (hlow y)
      simpa [Real.log_div] using h) x
  rw [leafSum_const] at hh
  calc
    Real.exp (-leafSum S (fun y => Real.log (1+t*D y)) x) ≤
        Real.exp ((leaves S : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = (2:ℝ) ^ leaves S := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]

theorem abs_fullyProtected_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    (G : Sample Ω S → ℝ) {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (ht : |t| ≤ 1/2) : |fullyProtected S T m D G t| ≤ B * (2:ℝ) ^ leaves S := by
  apply FiniteLaw.abs_expect_le
  intro x
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (hG x) (protected_density_bound S D hD ht x) (Real.exp_pos _).le hB

theorem abs_anchorEval_le {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {ι : Type} (A : Finset ι) (U : ι → Sample Ω S → FinitePath Ω n)
    (G : Sample Ω S → ℝ) {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B)
    (ht : |t| ≤ 1/2) : |anchorEval S T m D A U G t| ≤ B * (2:ℝ) ^ (leaves S + A.card) := by
  have hprod (x : Sample Ω S) : |∏ i ∈ A, (1+t*D (U i x))| ≤ (2:ℝ)^A.card := by
    rw [Finset.abs_prod]
    calc
      (∏ i ∈ A, |1+t*D (U i x)|) ≤ ∏ _i ∈ A, (2:ℝ) := Finset.prod_le_prod
        (fun i _ => abs_nonneg _) (fun i _ => by
          have hterm := abs_add_le (1:ℝ) (t*D (U i x))
          have ha := mul_le_mul_of_nonneg_left (hD (U i x)) (abs_nonneg t)
          rw [← abs_mul, mul_one] at ha
          simp only [abs_one] at hterm
          linarith)
      _ = (2:ℝ)^A.card := by simp
  have hh := abs_fullyProtected_le S T m D hD (fun x => G x * ∏ i ∈ A, (1+t*D (U i x)))
    (B := B * (2:ℝ)^A.card) (by positivity) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hG x) (hprod x) (abs_nonneg _) hB) ht
  simpa only [anchorEval, pow_add, mul_assoc, mul_comm, mul_left_comm] using hh

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem derivativeBound_nonneg (q k : ℕ) : 0 ≤ derivativeBound q k := by
  induction k generalizing q with
  | zero => exact pow_nonneg (by norm_num) _
  | succ k ih => exact mul_nonneg (Nat.cast_nonneg _) (ih _)

theorem derivativeBound_mono (k : ℕ) : Monotone (fun q => derivativeBound q k) := by
  induction k with
  | zero => exact fun a b hab => pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hab
  | succ k ih =>
    intro a b hab
    exact mul_le_mul (by exact_mod_cast hab) (ih (Nat.add_le_add_right hab 1))
      (derivativeBound_nonneg _ _) (Nat.cast_nonneg _)

variable {Ω : Type} [Fintype Ω]

/-- Uniform real control of the full OLD-or-FRESH derivative expansion.
No depth, number of kernel states, or base-disorder law enters the bound. -/
theorem abs_anchorIterate_le {n : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0 = 0)
    (hend : m (Fin.last n) = 1) (D : FinitePath Ω n → ℝ) (hD : ∀ y, |D y| ≤ 1)
    {ι : Type} [DecidableEq ι] (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    {B t : ℝ} (hB : 0 ≤ B) (hG : ∀ x, |G x| ≤ B) (ht : |t| ≤ 1/2) :
    |anchorIterate T m D k S A U G t| ≤ B * derivativeBound (leaves S + A.card) k := by
  induction k generalizing S A with
  | zero => exact abs_anchorEval_le S T m D hD A U G hB hG ht
  | succ k ih =>
    let q := leaves S + A.card
    let C := derivativeBound (q+1) k
    have hold (i : ι) :
        |anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t| ≤ B*C := by
      apply (ih S (A.erase i) U _ (fun x => by
        rw [abs_mul]
        exact (mul_le_mul (hG x) (hD _) (abs_nonneg _) hB).trans (by simp))).trans
      apply mul_le_mul_of_nonneg_left _ hB
      exact derivativeBound_mono k (by
        have hc := Finset.card_le_card (Finset.erase_subset i A)
        dsimp [q]
        omega)
    have hfresh (v : Internal S) :
        |anchorIterate T m D k (grow S v) A (fun i x => U i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x)) t| ≤ B*C := by
      have hh := ih (grow S v) A (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) (fun x => by
        rw [abs_mul]
        exact (mul_le_mul (hG _) (hD _) (abs_nonneg _) hB).trans (by simp))
      simpa only [C, q, leaves_grow, Nat.add_right_comm, Nat.add_assoc] using hh
    have h₁ : |∑ i ∈ A, anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t| ≤
        (A.card:ℝ)*(B*C) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ i ∈ A, |anchorIterate T m D k S (A.erase i) U (fun x => G x * D (U i x)) t|)
          ≤ ∑ _i ∈ A, B*C := Finset.sum_le_sum (fun i _ => hold i)
        _ = _ := by simp
    have h₂ : |∑ v : Internal S, gamma S m v * anchorIterate T m D k (grow S v) A
        (fun i x => U i (oldSample S v x))
        (fun x => G (oldSample S v x) * D (newPath S v x)) t| ≤
        (leaves S:ℝ)*(B*C) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ v : Internal S, |gamma S m v * anchorIterate T m D k (grow S v) A
          (fun i x => U i (oldSample S v x))
          (fun x => G (oldSample S v x) * D (newPath S v x)) t|)
          ≤ ∑ v : Internal S, |gamma S m v| * (B*C) := by
            apply Finset.sum_le_sum
            intro v _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hfresh v) (abs_nonneg _)
        _ = _ := by rw [← Finset.sum_mul, sum_abs_gamma S m hm hpos hroot hend]
    exact ((abs_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by
      dsimp [C, q, derivativeBound]
      push_cast
      ring)

end DilutedSpinGlass.PrescribedTree

open Filter Set
open scoped Topology BigOperators

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- Measurability of every finite prescribed-tree probability for the actual
recursively tilted conditional kernels. -/
theorem measurable_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (a : S.Sample Ω) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) := by
  induction S with
  | leaf => exact measurable_const
  | @node n k C ih =>
    change Measurable (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2)
    apply Finset.measurable_prod
    intro i _
    exact (T.1.measurable_tilt_weight (m 0)
      (fun z => KernelTower.measurable_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

theorem measurable_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) := by
  apply Finset.measurable_sum
  intro a _
  exact (measurable_tilt_sample_weight S T m hf a).mul (hg a)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalTaylor
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n : ℕ}

/-- Measurability of every coefficient of the actual finite extension
recursion, from measurable old-tree expectations. -/
theorem measurable_anchorIterate_zero (T : Z → KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (hT : ∀ (S : PrescribedTree n) (G : S.Sample Ω → ℝ),
      Measurable (fun z => (S.sampleLaw (T z)).expect G))
    (D : FinitePath Ω n → ℝ) {ι : Type} [DecidableEq ι]
    (k : ℕ) (S : PrescribedTree n) (A : Finset ι)
    (U : ι → S.Sample Ω → FinitePath Ω n) (G : S.Sample Ω → ℝ) :
    Measurable (fun z => anchorIterate (T z) m D k S A U G 0) := by
  induction k generalizing S A with
  | zero => simpa only [anchorIterate,anchorEval_zero S _ m hm] using hT S G
  | succ k ih =>
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun i _ => ih S (A.erase i) U _)
    · exact Finset.measurable_sum _ (fun v _ => (ih (grow S v) A _ _).const_mul _)

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

lemma measurable_externalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (k : ℕ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => externalCoefficient S a T Q m (base z) roots i old D E f k) := by
  unfold externalCoefficient PrescribedTree.anchorCoefficient
  apply Measurable.div_const
  apply PrescribedTree.measurable_anchorIterate_zero _ m hm
  intro S G
  simp_rw [← KernelTower.tilt_prod_fst]
  refine PrescribedTree.measurable_tilt_sample_expect S
    (KernelTower.prod L (tower roots L T Q) (markPrior L (Q i))) (fun j => m j.succ) ?_ ?_
  · exact fun y => (hb _).add measurable_const
  · exact fun x => measurable_const

variable (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B) (hD : ∀ x y, |D x y| ≤ 1) (hE : ∀ x y, |E x y| ≤ 1)

include hmono hpos hroot hend hB hf hD hE in
lemma externalCoefficient_bound (k : ℕ) :
    |externalCoefficient S a T Q m base roots i old D E f k| ≤
      B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) k/(k.factorial:ℝ) := by
  unfold externalCoefficient PrescribedTree.anchorCoefficient
  rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial:ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply PrescribedTree.abs_anchorIterate_le _ m hmono hpos hroot hend _ (fun y => hD _ _) k S _ _ _ hB
  · intro x
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul (hf _) (hE _ _) (abs_nonneg _) hB
  · norm_num

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

lemma measurable_rootExternalCoefficient (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j : Fin L, m j.succ ≠ 0)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (j : ℕ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × I => rootExternalCoefficient S a T Q m base old D E f j z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  dsimp only [rootExternalCoefficient]
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  exact measurable_externalCoefficient S a T Q m hm
    (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) i old (D i) (E i) f j (hb k)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniversalDictionary
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators


lemma table_bound {L r : ℕ} (g : Table L r) (y : Fin L → Fin r → Bool) :
    |(g.1 y : ℝ)| ≤ 1 := by exact_mod_cast g.2 y
lemma direction_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |direction q σ y| ≤ 1 := by
  rw [direction,abs_mul]
  have hs : |spin σ| = 1 := by cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _
lemma anchor_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |anchor q σ y| ≤ 1 := by
  rw [anchor,abs_mul]
  have hs : |(if q.2.2.2 then spin σ else 1 : ℝ)| = 1 := by
    split <;> cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExternalCoefficientLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma integrable_rootExternalCoefficient_label
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (label : Z → I) (hl : Measurable label) (k : ℕ) :
    Integrable (fun z : FullRootState Y X I M × Z =>
      rootExternalCoefficient S a T Q m base old D E f k z.1 (label z.2))
      ((fullRootLaw ξ μ ν r s).prod τ) := by
  apply Integrable.of_bound ((measurable_rootExternalCoefficient S a T Q m hm base old D E f k hb).comp
    (measurable_fst.prodMk (hl.comp measurable_snd))).aestronglyMeasurable
    (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) k/(k.factorial:ℝ))
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact externalCoefficient_bound S a T Q m hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) (label z.2) old _ _ f hB hf (hD _) (hE _) k)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConcreteHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree
open scoped NNReal BigOperators
variable {Ω X Y Z : Type} [Fintype Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z] {L M r k : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (Labels L Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (rate score : ℝ≥0)
    (S : PrescribedTree (L+1)) (anchorLeaf : S.Leaf)
    (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (base : RootPath Y M → (n : ℕ) → RootPath X n → FinitePath Ω (L+1) → ℝ)
    (old : (i : Labels L Z) → FinitePath Ω (L+1) → FinitePath (Alphabet i.1.1) (L+1) → ℝ)
    (read : Z → FinitePath Ω (L+1) → Spin)
    (a b : Fin r → Option (Fin k)) (d : Fin r → Fin L) (spinAnchor : Bool)
    (f : (S.Leaf → FinitePath Ω (L+1)) → ℝ)

variable (hb : ∀ n y, Measurable (fun z : RootPath Y M × RootPath X n => base z.1 n z.2 y))
    (hm : ∀ j : Fin (L+1), m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last (L+1)) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)

include hb hm hmono hpos hroot hend hB hf

lemma integrable_rootHistory_sat_oai (hk : 0 < k) :
    Integrable (fun z : FullRootState Y X (Labels L Z) M × Z =>
      rootHistory S anchorLeaf T m base old read a b d spinAnchor f z.1 z.2)
      ((fullRootLaw ξ μ ν rate score).prod τ) := by
  have hi (ε : Fin k → Bool) := integrable_rootExternalCoefficient_label ξ μ ν τ rate score
    S anchorLeaf T (fun i => prior i.1.1) m base old
    (fun i x y => direction i.1.1 (read i.2 x) y)
    (fun i x y => anchor i.1.1 (read i.2 x) y) f hb hm hmono hpos hroot hend hB hf
    (fun _ _ _ => direction_bound _ _ _) (fun _ _ _ => anchor_bound _ _ _)
    (fun v => ((polarizedSpec hk ε a b d spinAnchor,0),v))
    (measurable_const.prodMk measurable_id) k
  simp_rw [rootHistory_polarization_sat hk S anchorLeaf T m hm hroot hend base old read a b d spinAnchor f]
  exact (integrable_finsetSum _ (fun ε _ => (hi ε).const_mul _)).const_mul _

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat_oai := @OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat_oai

-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_fourBody_total_haar_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:34:06.489618+00:00
-- url     : https://prove2.me/submissions/b578635f-9534-410a-b58c-e1f1cb655873

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L002
import Theorems.Thm_OAI_Laughlin_Fock_limitFourCopyEnd_local_sum
import Theorems.Thm_OAI_Laughlin_Fock_physical_pair_norm_haar_real
import Theorems.Thm_OAI_Laughlin_Fock_source_fourBody_limitpositive

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pair_radicand_factorization (Q p x y : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hxy : x+y = p+1) :
    ((Q.descFactorial x : ℝ) / (Q : ℝ)^x) *
    ((Q.descFactorial y : ℝ) / (Q : ℝ)^y) *
    (((2 : ℝ)*Q)^p / ((2*Q-2).descFactorial p : ℝ)) *
    ((p.factorial : ℝ) / ((2 : ℝ)^p * (x.factorial : ℝ) * (y.factorial : ℝ))) =
    ((Q.descFactorial x : ℝ)*(Q.descFactorial y : ℝ)*(p.factorial : ℝ)) /
      ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(x.factorial : ℝ)*(y.factorial : ℝ)) := by
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hd : ((2*Q-2).descFactorial p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hp))
  have hx : (x.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.factorial : ℝ) ≠ 0 := by positivity
  have hh : (Q : ℝ)^x * (Q : ℝ)^y = (Q : ℝ)^p * Q := by
    rw [← pow_add, hxy, pow_succ]
  rw [mul_pow]
  field_simp
  have he := congrArg (fun t : ℝ => (Q.descFactorial x : ℝ) * (Q.descFactorial y : ℝ) * t) hh
  nlinarith only [he]

theorem pairCoefficient_conjugation (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    pairCoefficient Q p x y =
      modeFactor Q x.val * modeFactor Q y.val * pairFactor Q p *
        pairLimitCoefficient p x.val y.val := by
  unfold pairCoefficient pairLimitCoefficient modeFactor pairFactor
  split_ifs with h
  · have hr := pair_radicand_factorization Q p x.val y.val hQ hp h
    have hs := congrArg Real.sqrt hr
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)] at hs
    rw [← hs]
    ring_nf
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem contraction_map {Q : ℕ} (f : Orbital Q →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space Q) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

theorem projection_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalScaling Q d) = d i • LinearMap.proj i := by
  ext v
  rfl

theorem annihilate_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorScaling Q d x) = d i • exteriorScaling Q d (annihilate i x) := by
  unfold annihilate exteriorScaling
  rw [contraction_map, projection_scaling, map_smul, LinearMap.smul_apply, map_smul]

theorem exteriorScaling_inverse (Q : ℕ) (d : Fin (Q+1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (x : Space Q) : exteriorScaling Q (fun i => (d i)⁻¹) (exteriorScaling Q d x) = x := by
  have h : (orbitalScaling Q (fun i => (d i)⁻¹)).comp (orbitalScaling Q d) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    funext i
    change (d i)⁻¹*(d i*v i) = v i
    rw [← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  change ((ExteriorAlgebra.map (orbitalScaling Q (fun i => (d i)⁻¹))).comp
    (ExteriorAlgebra.map (orbitalScaling Q d))) x = x
  rw [ExteriorAlgebra.map_comp_map, h, ExteriorAlgebra.map_id]
  rfl

theorem modeFactor_pos (Q : ℕ) (hQ : 0 < Q) (i : Fin (Q+1)) : 0 < modeFactor Q i.val := by
  unfold modeFactor
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact_mod_cast (Nat.descFactorial_pos.mpr (show i.val ≤ Q by omega))
  · exact pow_pos (by exact_mod_cast hQ) _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_PairConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairEnd_smul (Q : ℕ) (r : ℂ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairEnd Q (fun i j => r*c i j) = r • pairEnd Q c := by
  simp only [pairEnd, Finset.smul_sum, smul_smul]

theorem pairEnd_scaling (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (d : Fin (Q+1) → ℂ) (x : Space Q) :
    pairEnd Q c (exteriorScaling Q d x) =
      exteriorScaling Q d (pairEnd Q (fun i j => c i j*d i*d j) x) := by
  simp only [pairEnd, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    map_sum, map_smul, annihilate_scaling, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_ScalingWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem orbitalScaling_mode (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    orbitalScaling Q d (mode i) = d i • mode i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [orbitalScaling,mode]
  · simp [orbitalScaling,mode,h]

theorem exteriorScaling_wedge (Q n : ℕ) (d : Fin (Q+1) → ℂ) (w : Fin n → Fin (Q+1)) :
    exteriorScaling Q d (ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a))) =
      (∏ a, d (w a)) • ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a)) := by
  unfold exteriorScaling
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ n (fun a => orbitalScaling Q d (mode (w a))) = _
  simp_rw [orbitalScaling_mode]
  exact (ExteriorAlgebra.ιMulti ℂ n).map_smul_univ (fun a => d (w a)) (fun a => mode (w a))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_OccupationDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_product (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    (∏ a : Fin n, d (Set.powersetCard.ofFinEmbEquiv.symm A a)) = ∏ i ∈ A.val, d i := by
  apply Finset.prod_bij (fun a _ => Set.powersetCard.ofFinEmbEquiv.symm A a)
  · intro a ha
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A _).mp ⟨a,rfl⟩
  · intro a ha b hb hab
    exact (Set.powersetCard.ofFinEmbEquiv.symm A).injective hab
  · intro b hb
    obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A b).mpr hb
    exact ⟨a, Finset.mem_univ a, ha⟩
  · intro a ha
    rfl

theorem exteriorScaling_occupation_sector (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    exteriorScaling Q d (occupationBasis Q A.val) =
      (∏ i ∈ A.val, d i) • occupationBasis Q A.val := by
  have h := exteriorScaling_wedge Q n d (Set.powersetCard.ofFinEmbEquiv.symm A)
  rw [occupation_product Q n d A] at h
  simpa only [occupationBasis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem exteriorScaling_occupation (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Finset (Fin (Q+1))) :
    exteriorScaling Q d (occupationBasis Q A) = (∏ i ∈ A, d i) • occupationBasis Q A := by
  exact exteriorScaling_occupation_sector Q A.card d ⟨A,rfl⟩

theorem exteriorScaling_occupation_entry (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A B : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (exteriorScaling Q d (occupationBasis Q A)) B =
      if A = B then ∏ i ∈ A, d i else 0 := by
  rw [exteriorScaling_occupation, map_smul]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem exteriorScaling_coordinate (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (exteriorScaling Q d x) A =
      (∏ i ∈ A, d i)*(occupationBasis Q).repr x A := by
  have h : ((occupationBasis Q).coord A).comp (exteriorScaling Q d).toLinearMap =
      (∏ i ∈ A, d i) • (occupationBasis Q).coord A := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (exteriorScaling Q d (occupationBasis Q B)) A =
      (∏ i ∈ A, d i)*(occupationBasis Q).repr (occupationBasis Q B) A
    rw [exteriorScaling_occupation_entry]
    by_cases hBA : B = A
    · subst B
      simp
    · simp [Module.Basis.repr_self, hBA]
  exact LinearMap.congr_fun h x

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_LocalMetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem localMetricError_nonneg (L Q : ℕ) : 0 ≤ localMetricError L Q := norm_nonneg _

theorem localMetricError_bound (L Q : ℕ) (A : Finset (Fin (L+1))) :
    |((localDiagonals L Q A)⁻¹)^2-1| ≤ localMetricError L Q := by
  have h := norm_le_pi_norm (fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2-1) A
  change ‖((localDiagonals L Q A)⁻¹)^2-1‖ ≤ localMetricError L Q at h
  rw [Real.norm_eq_abs] at h
  exact h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators InnerProductSpace

theorem quadratic_perturbation_bound {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : ι → ι → ℝ) (x : ι → F) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ i j, |R i j| ≤ ε) :
    |∑ i, ∑ j, R i j * ⟪x i, x j⟫_ℝ| ≤
      ε * (Fintype.card ι : ℝ) * ∑ i, ‖x i‖^2 := by
  have hp (i j : ι) :
      |R i j * ⟪x i, x j⟫_ℝ| ≤ ε * (‖x i‖^2 + ‖x j‖^2) / 2 := by
    rw [abs_mul]
    have hi : |⟪x i, x j⟫_ℝ| ≤ (‖x i‖^2 + ‖x j‖^2)/2 := by
      have hc := abs_real_inner_le_norm (x i) (x j)
      nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
    calc
      |R i j| * |⟪x i, x j⟫_ℝ| ≤ ε * ((‖x i‖^2 + ‖x j‖^2)/2) :=
        mul_le_mul (hR i j) hi (abs_nonneg _) hε
      _ = _ := by ring
  calc
    |∑ i, ∑ j, R i j * ⟪x i, x j⟫_ℝ| ≤
        ∑ i, ∑ j, |R i j * ⟪x i, x j⟫_ℝ| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i : ι, ∑ j : ι, ε * (‖x i‖^2 + ‖x j‖^2) / 2 := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp only [mul_add, add_div, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring_nf
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) : annihilate i (occupationBasis Q A) = 0 := by
  let d : Fin (Q+1) → ℂ := fun j => if j = i then 0 else 1
  have hd : (∏ j ∈ A, d j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [d, show j ≠ i by intro h; subst j; exact hi hj]
  have h := annihilate_scaling Q d i (occupationBasis Q A)
  rw [exteriorScaling_occupation,hd,one_smul] at h
  simpa [d] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem insertionSign_spec (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A = 1 ∨ insertionSign Q i A = -1 := by
  by_cases h : i ∉ A
  · simpa [insertionSign,h] using (create_unoccupied_sign Q i A h).choose_spec.1
  · simp [insertionSign,h]

theorem insertionSign_sq (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A * insertionSign Q i A = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem insertionSign_norm (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    ‖insertionSign Q i A‖ = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    create i (occupationBasis Q A) = insertionSign Q i A • occupationBasis Q (insert i A) := by
  simpa [insertionSign,hi] using (create_unoccupied_sign Q i A hi).choose_spec.2

theorem annihilate_insert (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    annihilate i (occupationBasis Q (insert i A)) = insertionSign Q i A • occupationBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (occupationBasis Q A)
  change annihilate i (create i (occupationBasis Q A)) +
    create i (annihilate i (occupationBasis Q A)) = (if i = i then (1 : ℂ) else 0) • occupationBasis Q A at h
  rw [create_unoccupied Q i A hi, map_smul, annihilate_unoccupied Q i A hi, map_zero] at h
  simp only [add_zero, ite_true, one_smul] at h
  have he := congrArg (fun x => insertionSign Q i A • x) h
  simpa only [smul_smul, insertionSign_sq, one_smul] using he

theorem annihilate_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) :
    annihilate i (occupationBasis Q A) =
      insertionSign Q i (A.erase i) • occupationBasis Q (A.erase i) := by
  simpa only [Finset.insert_erase hi] using
    annihilate_insert Q i (A.erase i) (Finset.notMem_erase i A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (annihilate i x) A =
      if i ∈ A then 0 else insertionSign Q i A * (occupationBasis Q).repr x (insert i A) := by
  let e : ℂ := if i ∈ A then 0 else insertionSign Q i A
  have h : ((occupationBasis Q).coord A).comp (annihilate i) =
      e • (occupationBasis Q).coord (insert i A) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (annihilate i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (insert i A)
    by_cases hiB : i ∈ B
    · rw [annihilate_occupied Q i B hiB, map_smul, Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · have hBA : B.erase i ≠ A := by intro h; rw [← h] at hiA; exact Finset.notMem_erase i B hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hBA]
      · by_cases hBA : B = insert i A
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have herase : B.erase i ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.insert_erase hiB]
          simp [e,hiA,Module.Basis.repr_self,herase,hBA]
    · rw [annihilate_unoccupied Q i B hiB]
      have hBA : B ≠ insert i A := by intro h; subst B; simp at hiB
      simp [e,Module.Basis.repr_self,hBA]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_ContractionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

theorem annihilate_normSq (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) =
      ∑ A : Finset (Fin (Q+1)), if i ∈ A then ‖(occupationBasis Q).repr x A‖^2 else 0 := by
  have h (A : Finset (Fin (Q+1))) :
      ‖(occupationBasis Q).repr (annihilate i x) A‖^2 =
        if i ∉ A then ‖(occupationBasis Q).repr x (insert i A)‖^2 else 0 := by
    by_cases hi : i ∈ A <;> simp [annihilate_coordinate,hi,insertionSign_norm]
  unfold occupationNormSq
  simp_rw [h]
  simpa only [Finset.sum_filter] using
    sum_unoccupied_insert (R := ℝ) i (fun A => ‖(occupationBasis Q).repr x A‖^2)

theorem annihilate_normSq_le (Q : ℕ) (i : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate i x) ≤ occupationNormSq Q x := by
  rw [annihilate_normSq]
  unfold occupationNormSq
  apply Finset.sum_le_sum
  intro A hA
  split_ifs
  · exact le_rfl
  · positivity

theorem two_annihilate_normSq_le (Q : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (annihilate k (annihilate j x)) ≤ occupationNormSq Q x :=
  (annihilate_normSq_le Q k _).trans (annihilate_normSq_le Q j x)

theorem limitFour_normSq_le_pair (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    occupationNormSq Q (limitFourEnd Q p j k x) ≤
      occupationNormSq Q (limitPairEnd Q p x) :=
  two_annihilate_normSq_le Q j k (limitPairEnd Q p x)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CollectionAnnihilatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem collection_limit_annihilator_bound {I : Type*} [Fintype I] (Q : ℕ)
    (p : I → ℕ) (j k : I → Fin (Q+1)) (hp : ∀ i, p i ≤ 23) (x : Space Q) :
    (∑ i, occupationNormSq Q (limitFourEnd Q (p i) (j i) (k i) x)) ≤
      (Fintype.card I : ℝ) * limitPairWindow Q x := by
  calc
    _ ≤ ∑ i : I, limitPairWindow Q x := by
      apply Finset.sum_le_sum
      intro i hi
      apply (limitFour_normSq_le_pair Q (p i) (j i) (k i) x).trans
      change occupationNormSq Q (limitPairEnd Q (p i) x) ≤
        ∑ r ∈ Finset.range 24, occupationNormSq Q (limitPairEnd Q r x)
      exact Finset.single_le_sum
        (f := fun r => occupationNormSq Q (limitPairEnd Q r x))
        (fun r hr => occupationNormSq_nonneg Q _) (Finset.mem_range.mpr (by have h := hp i; omega))
    _ = _ := by simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_FactorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem modeFactor_le_one (Q x : ℕ) (hQ : 0 < Q) : modeFactor Q x ≤ 1 := by
  have hpow : (0 : ℝ) < (Q : ℝ)^x := pow_pos (by exact_mod_cast hQ) _
  have hd : (Q.descFactorial x : ℝ) ≤ (Q : ℝ)^x := by
    exact_mod_cast Nat.descFactorial_le_pow Q x
  have h := Real.sqrt_le_sqrt ((div_le_one hpow).mpr hd)
  simpa [modeFactor] using h

theorem pairFactor_one_le (Q p : ℕ) (hp : p ≤ 2*Q-2) : 1 ≤ pairFactor Q p := by
  have hd : (0 : ℝ) < (2*Q-2).descFactorial p := by exact_mod_cast Nat.descFactorial_pos.mpr hp
  have hn : (2*Q-2).descFactorial p ≤ (2*Q)^p := by
    apply (Nat.descFactorial_le_pow (2*Q-2) p).trans
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) p
  have hr : ((2*Q-2).descFactorial p : ℝ) ≤ ((2 : ℝ)*Q)^p := by exact_mod_cast hn
  have h := Real.sqrt_le_sqrt ((one_le_div hd).mpr hr)
  simpa [pairFactor] using h

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_EnergyReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationNormSq_smul (Q : ℕ) (c : ℂ) (x : Space Q) :
    occupationNormSq Q (c • x) = ‖c‖^2 * occupationNormSq Q x := by
  simp [occupationNormSq,mul_pow,Finset.mul_sum]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_TruncatedScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncatedModeFactor_pos (L Q : ℕ) (hQ : 0 < Q) (i : Fin (Q+1)) :
    0 < truncatedModeFactor L Q i := by
  unfold truncatedModeFactor
  split_ifs
  · exact modeFactor_pos Q hQ i
  · norm_num

theorem truncatedScaling_left_inverse (L Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    truncatedScalingInv L Q (truncatedScaling L Q x) = x := by
  apply exteriorScaling_inverse
  intro i
  exact_mod_cast ne_of_gt (truncatedModeFactor_pos L Q hQ i)

theorem truncatedDiagonals_local (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) :
    truncatedDiagonals L Q A = localDiagonals L Q (localOccupation L Q hL A) := by
  classical
  unfold truncatedDiagonals truncatedModeFactor localDiagonals
  rw [← Finset.prod_filter]
  symm
  apply Finset.prod_bij (fun i hi => (⟨i.val,by have := i.isLt; omega⟩ : Fin (Q+1)))
  · intro i hi
    simp only [localOccupation,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    exact Finset.mem_filter.mpr ⟨hi,by change i.val ≤ L; have := i.isLt; omega⟩
  · intro i hi j hj he
    exact Fin.ext (congrArg (@Fin.val (Q+1)) he)
  · intro i hi
    obtain ⟨hiA,hiL⟩ := Finset.mem_filter.mp hi
    refine ⟨⟨i.val,by omega⟩,?_,?_⟩
    · simpa [localOccupation] using hiA
    · rfl
  · intro i hi
    rfl

theorem truncatedScalingInv_coordinate (L Q : ℕ) (x : Space Q) (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (truncatedScalingInv L Q x) A =
      ((truncatedDiagonals L Q A)⁻¹ : ℝ) * (occupationBasis Q).repr x A := by
  rw [truncatedScalingInv,exteriorScaling_coordinate]
  simp [truncatedDiagonals,Finset.prod_inv_distrib,Complex.ofReal_prod]

theorem truncatedMetricError_bound (L Q : ℕ) (hL : L ≤ Q) (A : Finset (Fin (Q+1))) :
    |((truncatedDiagonals L Q A)⁻¹)^2-1| ≤ localMetricError L Q := by
  rw [truncatedDiagonals_local L Q hL]
  exact localMetricError_bound L Q _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem occupation_coefficient_perturbation {I : Type*} [Fintype I] (Q : ℕ)
    (R : Finset (Fin (Q+1)) → I → I → ℝ) (v : I → Space Q)
    (ε : ℝ) (hε : 0 ≤ ε) (hR : ∀ A i j, |R A i j| ≤ ε) :
    |∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j, R A i j *
      ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, occupationNormSq Q (v i) := by
  calc
    _ ≤ ∑ A : Finset (Fin (Q+1)), |∑ i, ∑ j, R A i j *
        ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A : Finset (Fin (Q+1)), ε * (Fintype.card I : ℝ) *
        ∑ i, ‖(occupationBasis Q).repr (v i) A‖^2 :=
      Finset.sum_le_sum (fun A hA => quadratic_perturbation_bound (R A)
        (fun i => (occupationBasis Q).repr (v i) A) ε hε (hR A))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_TruncatedMetricPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem occupationQuadratic_coordinates {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (v : I → Space Q) :
    occupationQuadratic Q R v = ∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j,
      R i j * ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ := by
  simp only [occupationQuadratic,occupationInner,Finset.mul_sum,Complex.re_sum,
    Complex.inner,Complex.star_def]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A hA
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem truncatedQuadratic_error {I : Type*} [Fintype I] (L Q : ℕ)
    (R S : I → I → ℝ) (v : I → Space Q) (ε : ℝ) (hε : 0 ≤ ε)
    (hR : ∀ A : Finset (Fin (Q+1)), ∀ i j,
      |((truncatedDiagonals L Q A)⁻¹)^2 * R i j - S i j| ≤ ε) :
    |occupationQuadratic Q R (fun i => truncatedScalingInv L Q (v i)) - occupationQuadratic Q S v| ≤
      ε * (Fintype.card I : ℝ) * ∑ i, occupationNormSq Q (v i) := by
  have he : occupationQuadratic Q R (fun i => truncatedScalingInv L Q (v i)) - occupationQuadratic Q S v =
      ∑ A : Finset (Fin (Q+1)), ∑ i, ∑ j,
        (((truncatedDiagonals L Q A)⁻¹)^2 * R i j - S i j) *
          ⟪(occupationBasis Q).repr (v i) A,(occupationBasis Q).repr (v j) A⟫_ℝ := by
    rw [occupationQuadratic_coordinates,occupationQuadratic_coordinates,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro A hA
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j hj
    rw [truncatedScalingInv_coordinate,truncatedScalingInv_coordinate]
    simp only [Complex.inner,map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    ring
  rw [he]
  exact occupation_coefficient_perturbation Q _ v ε hε hR

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Compact
attribute [-instance] _root_.OAI.Laughlin.Rotation.sourceHaar_isHaar _root_.OAI.Laughlin.Rotation.sourceHaar_isProbability _root_.OAI.Laughlin.Rotation.sourceSU2_borelSpace _root_.OAI.Laughlin.Rotation.sourceSU2_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceTensorRepresentation_continuous (Q : ℕ) (a b : Fin Q → Fin 2) :
    Continuous (fun g : SourceSU2 => sourceTensorRepresentation Q g a b) := by
  change Continuous (fun g : SourceSU2 => ∏ i, g.val (a i) (b i))
  exact continuous_finsetProd _ (fun i hi => (continuous_apply (b i)).comp
    ((continuous_apply (a i)).comp continuous_subtype_val))

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

 theorem sourceSpinRepresentation_continuous (Q : ℕ) (p q : Fin (Q+1)) :
    Continuous (fun g => sourceSpinRepresentation Q g p q) := by
  change Continuous (fun g : SourceSU2 =>
    ((symmetricTensorInclusion Q)ᴴ*sourceTensorRepresentation Q g*symmetricTensorInclusion Q) p q)
  simp only [Matrix.mul_apply]
  have h := sourceTensorRepresentation_continuous Q
  fun_prop

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_SpinAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbital_sum_modes (Q : ℕ) (v : Orbital Q) : v = ∑ i, v i • mode i := by
  funext j
  simp [mode,Pi.single_apply]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_MatrixQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem occupation_matrix_quadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (W : Matrix J I ℂ) (C : Matrix I I ℂ) (v : J → Space Q) :
    (∑ i, ∑ j, C i j * occupationInner Q
      (∑ a, star (W a i) • v a) (∑ b, star (W b j) • v b)) =
      ∑ a, ∑ b, (W*C*Wᴴ) a b * occupationInner Q (v a) (v b) := by
  simp_rw [occupationInner_sum_left,occupationInner_smul_left,star_star,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Tensor_ExteriorRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Rotation

theorem orbitalRotation_mode (Q : ℕ) (g : SourceSU2) (i : Fin (Q+1)) :
    orbitalRotation Q g (mode i) = ∑ j, sourceSpinRepresentation Q g j i • mode j := by
  rw [orbital_sum_modes Q (orbitalRotation Q g (mode i))]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp [orbitalRotation,mode,Matrix.mulVec,dotProduct,Pi.single_apply]

theorem exteriorRotation_basis_wedge (N Q : ℕ) (g : SourceSU2) (a : Configuration N Q) :
    exteriorRotation Q g (ExteriorAlgebra.ιMulti ℂ N (fun k => mode (a k))) =
      ∑ b : Configuration N Q, (∏ k, sourceSpinRepresentation Q g (b k) (a k)) •
        ExteriorAlgebra.ιMulti ℂ N (fun k => mode (b k)) := by
  unfold exteriorRotation
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ N (fun k => orbitalRotation Q g (mode (a k))) = _
  simp_rw [orbitalRotation_mode]
  change (ExteriorAlgebra.ιMulti ℂ N).toMultilinearMap
    (fun k => ∑ j, sourceSpinRepresentation Q g j (a k) • mode j) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact (ExteriorAlgebra.ιMulti ℂ N).map_smul_univ _ _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_SpinContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators

theorem occupationBasis_wedge (Q : ℕ) (A : Finset (Fin (Q+1))) :
    occupationBasis Q A = ExteriorAlgebra.ιMulti ℂ A.card
      (fun k => mode (Set.powersetCard.ofFinEmbEquiv.symm (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) k)) := by
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card).val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family,Function.comp_def,Pi.basisFun_apply,mode]

theorem exteriorRotation_basis_continuous (Q : ℕ) (A B : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr
      (exteriorRotation Q g (occupationBasis Q B)) A) := by
  simp only [occupationBasis_wedge Q B,exteriorRotation_basis_wedge,map_sum,map_smul,
    Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  apply continuous_finsetSum
  intro b hb
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro k hk
  exact sourceSpinRepresentation_continuous Q _ _

theorem exteriorRotation_coordinate_continuous (Q : ℕ) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr (exteriorRotation Q g x) A) := by
  have hx := (occupationBasis Q).sum_repr x
  conv in exteriorRotation Q _ x => rw [← hx]
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  apply continuous_finsetSum
  intro b hb
  exact continuous_const.mul (exteriorRotation_basis_continuous Q A b)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_OrbitIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators

theorem linearMap_rotation_coordinate_continuous (Q : ℕ) (L : Module.End ℂ (Space Q))
    (x : Space Q) (A : Finset (Fin (Q+1))) :
    Continuous (fun g : SourceSU2 => (occupationBasis Q).repr (L (exteriorRotation Q g⁻¹ x)) A) := by
  have he (g : SourceSU2) : (occupationBasis Q).repr (L (exteriorRotation Q g⁻¹ x)) A =
      ∑ B, (occupationBasis Q).repr (exteriorRotation Q g⁻¹ x) B *
        (occupationBasis Q).repr (L (occupationBasis Q B)) A := by
    conv_lhs => rw [← (occupationBasis Q).sum_repr (exteriorRotation Q g⁻¹ x)]
    simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro B hB
  exact ((exteriorRotation_coordinate_continuous Q x B).comp continuous_inv).mul continuous_const

theorem linearMap_rotation_norm_continuous (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) :
    Continuous (fun g : SourceSU2 => occupationNormSq Q (L (exteriorRotation Q g⁻¹ x))) := by
  unfold occupationNormSq
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q L x A).norm.pow 2

theorem linearMap_rotation_norm_integrable (Q : ℕ) (L : Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationNormSq Q (L (exteriorRotation Q g⁻¹ x))) sourceHaar :=
  (linearMap_rotation_norm_continuous Q L x).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem sourcePairWindow_haar (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    (2*Q-2+1 : ℕ) * (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar) =
      24 * sourceFockEnergy Q x := by
  unfold sourcePairWindow
  rw [integral_finsetSum _ (fun p hp => linearMap_rotation_norm_integrable Q _ x)]
  have hp (p : ℕ) (h : p ∈ Finset.range 24) :
      (∫ g, occupationNormSq Q (sourcePairEnd Q p (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) =
      sourceFockEnergy Q x/(2*Q-2+1 : ℕ) :=
    physical_pair_norm_haar_real Q (by omega) ⟨p,by simp only [Finset.mem_range] at h; omega⟩ x
  rw [Finset.sum_congr rfl hp]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hd : ((2*Q-2+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CopyQuadraticMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix
open Matrix

theorem occupationQuadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (C : I → I → ℝ) (β : I → J → ℝ) (v : J → Space Q) :
    occupationQuadratic Q C (fun i => ∑ a, (β i a : ℂ) • v a) =
      occupationQuadratic Q (copyQuadraticMatrix C β) v := by
  let W : Matrix J I ℂ := fun a i => (β i a : ℂ)
  let C' : Matrix I I ℂ := fun i j => (C i j : ℂ)
  have hm (a b : J) : (W*C'*Wᴴ) a b = (copyQuadraticMatrix C β a b : ℂ) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
    simp only [W,C',Complex.star_def,Complex.conj_ofReal,copyQuadraticMatrix,Complex.ofReal_sum,Complex.ofReal_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  have h := occupation_matrix_quadratic_factor Q W C' v
  simp only [W,Complex.star_def,Complex.conj_ofReal,hm] at h
  exact congrArg Complex.re h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_MatrixMetricError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem entrySum_nonneg {I : Type*} [Fintype I] (R : I → I → ℝ) : 0 ≤ entrySum R := by
  unfold entrySum
  positivity

theorem abs_le_entrySum {I : Type*} [Fintype I] (R : I → I → ℝ) (i j : I) : |R i j| ≤ entrySum R := by
  apply (Finset.single_le_sum (fun k hk => abs_nonneg (R i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k hk => Finset.sum_nonneg (fun l hl => abs_nonneg (R k l))) (Finset.mem_univ i)

theorem matrixMetricError_nonneg {I : Type*} [Fintype I] (L Q : ℕ) (R S : I → I → ℝ) :
    0 ≤ matrixMetricError L Q R S :=
  add_nonneg (entrySum_nonneg _) (mul_nonneg (localMetricError_nonneg L Q) (entrySum_nonneg R))

theorem matrixMetricError_bound {I : Type*} [Fintype I] (L Q : ℕ) (hL : L ≤ Q)
    (R S : I → I → ℝ) (A : Finset (Fin (Q+1))) (i j : I) :
    |((truncatedDiagonals L Q A)⁻¹)^2*R i j-S i j| ≤ matrixMetricError L Q R S := by
  have he : ((truncatedDiagonals L Q A)⁻¹)^2*R i j-S i j =
      (((truncatedDiagonals L Q A)⁻¹)^2-1)*R i j+(R i j-S i j) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have h₁ := mul_le_mul (truncatedMetricError_bound L Q hL A) (abs_le_entrySum R i j)
    (abs_nonneg _) (localMetricError_nonneg L Q)
  have h₂ := abs_le_entrySum (fun i j => R i j-S i j) i j
  unfold matrixMetricError
  linarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TransferCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem fourBodyRho_nonneg (D Q : ℕ) : 0 ≤ fourBodyRho D Q :=
  mul_nonneg (matrixMetricError_nonneg _ _ _ _) (sq_nonneg _)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_TruncatedConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem truncated_sourcePair_intertwining (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (x : Space Q) :
    truncatedScaling L Q (sourcePairEnd Q p x) =
      (pairFactor Q p : ℂ) • limitPairEnd Q p (truncatedScaling L Q x) := by
  have hc : (fun i j : Fin (Q+1) => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) =
      (fun i j => (pairFactor Q p : ℂ)*
        (((pairLimitCoefficient p i.val j.val / Real.sqrt 2 : ℝ) : ℂ)*
          (truncatedModeFactor L Q i : ℂ)*(truncatedModeFactor L Q j : ℂ))) := by
    funext i j
    rw [pairCoefficient_conjugation Q p hQ hp]
    by_cases hs : i.val+j.val=p+1
    · simp only [truncatedModeFactor,ite_eq_left (show i.val≤L by omega),ite_eq_left (show j.val≤L by omega)]
      push_cast
      ring
    · simp [pairLimitCoefficient,hs]
  unfold sourcePairEnd limitPairEnd truncatedScaling
  rw [hc,pairEnd_smul,LinearMap.smul_apply,map_smul,pairEnd_scaling]

theorem truncated_sourceFour_conjugation (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (j k : Fin (Q+1))
    (hjL : j.val ≤ L) (hkL : k.val ≤ L) (x : Space Q) :
    sourceFourEnd Q p j k x =
      ((pairFactor Q p : ℂ)/((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))) •
        truncatedScalingInv L Q (limitFourEnd Q p j k (truncatedScaling L Q x)) := by
  have h := congrArg (fun y => annihilate k (annihilate j y))
    (truncated_sourcePair_intertwining L Q p hQ hp hL x)
  have he : ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) •
      truncatedScaling L Q (sourceFourEnd Q p j k x) =
        (pairFactor Q p : ℂ) • limitFourEnd Q p j k (truncatedScaling L Q x) := by
    simpa only [sourceFourEnd,limitFourEnd,Module.End.mul_apply,truncatedScaling,
      annihilate_scaling,map_smul,smul_smul,truncatedModeFactor,ite_eq_left hjL,ite_eq_left hkL] using h
  have h' := congrArg (truncatedScalingInv L Q) he
  rw [map_smul,truncatedScaling_left_inverse L Q hQ,map_smul] at h'
  have hj : (modeFactor Q j.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ j)
  have hk : (modeFactor Q k.val : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (modeFactor_pos Q hQ k)
  have hd := mul_ne_zero hj hk
  calc
    _ = ((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ))⁻¹ •
        (((modeFactor Q j.val : ℂ)*(modeFactor Q k.val : ℂ)) • sourceFourEnd Q p j k x) := by
      rw [smul_smul,inv_mul_cancel₀ hd,one_smul]
    _ = _ := by rw [h',smul_smul]; congr 1; ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_TruncatedFourCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

theorem physicalFourCopyEnd_truncated (Q r D : ℕ) (hDQ : D ≤ Q) (hQ : 24 ≤ Q)
    (hD : D ≤ 23) (x : Space Q) :
    physicalFourCopyEnd Q r D hDQ x = truncatedScalingInv 24 Q
      (∑ b : LocalFourIndex D, (physicalFourBeta Q r D b : ℂ) •
        localFourOperators Q D hDQ b (truncatedScaling 24 Q x)) := by
  simp only [physicalFourCopyEnd,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,localFourOperators]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncated_sourceFour_conjugation 24 Q b.val.1.val (by omega) (by omega) (by omega)
    _ _ (by change b.val.2.1.val ≤ 24; omega) (by change b.val.2.2.val ≤ 24; omega)]
  rw [smul_smul]
  congr 1
  simp only [physicalFourBeta]
  push_cast
  ring

theorem localFourOperators_bound (Q D : ℕ) (hDQ : D ≤ Q) (hD : D ≤ 23) (x : Space Q) :
    (∑ b : LocalFourIndex D, occupationNormSq Q (localFourOperators Q D hDQ b x)) ≤
      (Fintype.card (LocalFourIndex D) : ℝ) * limitPairWindow Q x := by
  exact collection_limit_annihilator_bound Q (fun b : LocalFourIndex D => b.val.1.val)
    (fun b => ⟨b.val.2.1.val,by omega⟩) (fun b => ⟨b.val.2.2.val,by omega⟩)
    (fun b => by have := b.val.1.isLt; omega) x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_TruncatedPairReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem truncatedScaling_normSq_le (L Q : ℕ) (hQ : 0 < Q) (x : Space Q) :
    occupationNormSq Q (truncatedScaling L Q x) ≤ occupationNormSq Q x := by
  unfold occupationNormSq truncatedScaling
  apply Finset.sum_le_sum
  intro A hA
  rw [exteriorScaling_coordinate,norm_mul,mul_pow]
  have hb : ‖∏ i ∈ A, (truncatedModeFactor L Q i : ℂ)‖ ≤ 1 := by
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro i hi; exact norm_nonneg _
    · intro i hi
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (truncatedModeFactor_pos L Q hQ i)]
      unfold truncatedModeFactor
      split_ifs
      · exact modeFactor_le_one Q i.val hQ
      · exact le_rfl
  have hsq : ‖∏ i ∈ A, (truncatedModeFactor L Q i : ℂ)‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hb 2
  exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans_eq (one_mul _)

theorem truncated_pair_energy_return (L Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (hL : p+1 ≤ L) (x : Space Q) :
    occupationNormSq Q (limitPairEnd Q p (truncatedScaling L Q x)) ≤
      occupationNormSq Q (sourcePairEnd Q p x) := by
  have he := congrArg (occupationNormSq Q) (truncated_sourcePair_intertwining L Q p hQ hp hL x)
  rw [occupationNormSq_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ pairFactor Q p from Real.sqrt_nonneg _)] at he
  have hr := pairFactor_one_le Q p hp
  have hsq : 1 ≤ (pairFactor Q p)^2 := by nlinarith
  calc
    _ ≤ (pairFactor Q p)^2 * occupationNormSq Q (limitPairEnd Q p (truncatedScaling L Q x)) := by
      simpa using mul_le_mul_of_nonneg_right hsq (occupationNormSq_nonneg Q _)
    _ = occupationNormSq Q (truncatedScaling L Q (sourcePairEnd Q p x)) := he.symm
    _ ≤ _ := truncatedScaling_normSq_le L Q hQ _

theorem truncated_pair_window_return (Q : ℕ) (hQ : 24 ≤ Q) (x : Space Q) :
    limitPairWindow Q (truncatedScaling 24 Q x) ≤ sourcePairWindow Q x := by
  unfold limitPairWindow sourcePairWindow
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_range.mp hp
  exact truncated_pair_energy_return 24 Q p (by omega) (by omega) (by omega) x

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_UniformTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter Spin

theorem source_fourBody_uniform_transfer (Q D : ℕ) (hQ : 24 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(fourBodyRho D Q * sourcePairWindow Q x) ≤
      occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega) x) := by
  let hDQ : D ≤ Q := by omega
  let v : LocalFourIndex D → Space Q := fun b =>
    localFourOperators Q D hDQ b (truncatedScaling 24 Q x)
  let ε := matrixMetricError 24 Q (finiteLocalFourMatrix Q D) (limitLocalFourMatrix D)
  let n : ℝ := Fintype.card (LocalFourIndex D)
  have hε : 0 ≤ ε := matrixMetricError_nonneg _ _ _ _
  have hn : 0 ≤ n := by positivity
  have hfinite : occupationQuadratic Q (finiteFourMiddle Q D)
      (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D hDQ x) =
      occupationQuadratic Q (finiteLocalFourMatrix Q D) (fun b => truncatedScalingInv 24 Q (v b)) := by
    simp_rw [physicalFourCopyEnd_truncated Q _ D hDQ hQ hD₂ x,map_sum,map_smul]
    exact occupationQuadratic_factor Q (finiteFourMiddle Q D) _ _
  rw [hfinite]
  have hbase := source_fourBody_limitpositive Q D (by omega) hD₁ hD₂ (truncatedScaling 24 Q x)
  change 0 ≤ occupationQuadratic Q (limitFourMiddle D)
    (fun i => limitFourCopyEnd Q (Certificate.copyLabel i) D (truncatedScaling 24 Q x)) at hbase
  have hends (i : Fin ((D+1)/2)) :
      limitFourCopyEnd Q (Certificate.copyLabel i) D (truncatedScaling 24 Q x) =
        ∑ b : LocalFourIndex D,
          (fourBodyLimitCoefficient (Certificate.copyLabel i) D D
            b.val.1.val b.val.2.1.val b.val.2.2.val : ℂ) • v b := by
    apply limitFourCopyEnd_local_sum Q _ D hDQ
    · unfold Certificate.copyLabel; have := i.isLt; omega
    · exact ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  simp_rw [hends] at hbase
  have hbase := hbase.trans_eq (occupationQuadratic_factor Q (limitFourMiddle D)
    (fun (i : Fin ((D+1)/2)) (b : LocalFourIndex D) =>
      fourBodyLimitCoefficient (Certificate.copyLabel i) D D b.val.1.val b.val.2.1.val b.val.2.2.val) v)
  change 0 ≤ occupationQuadratic Q (limitLocalFourMatrix D) v at hbase
  have herr := truncatedQuadratic_error 24 Q (finiteLocalFourMatrix Q D)
    (limitLocalFourMatrix D) v ε hε (matrixMetricError_bound 24 Q hQ _ _)
  have hpair : (∑ b, occupationNormSq Q (v b)) ≤ n * sourcePairWindow Q x := by
    apply (localFourOperators_bound Q D hDQ hD₂ (truncatedScaling 24 Q x)).trans
    exact mul_le_mul_of_nonneg_left (truncated_pair_window_return Q hQ x) hn
  have hbound : |occupationQuadratic Q (finiteLocalFourMatrix Q D) (fun b => truncatedScalingInv 24 Q (v b)) -
      occupationQuadratic Q (limitLocalFourMatrix D) v| ≤ fourBodyRho D Q * sourcePairWindow Q x := by
    apply herr.trans
    calc
      _ ≤ ε*n*(n*sourcePairWindow Q x) := mul_le_mul_of_nonneg_left hpair (mul_nonneg hε hn)
      _ = _ := by change ε*n*(n*sourcePairWindow Q x)=(ε*n^2)*sourcePairWindow Q x; ring
  have hl := (abs_le.mp hbound).1
  linarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_HaarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Topology

theorem occupationQuadratic_rotation_integrable {I : Type*} [Fintype I]
    (Q : ℕ) (R : I → I → ℝ) (L : I → Module.End ℂ (Space Q)) (x : Space Q) :
    Integrable (fun g : SourceSU2 => occupationQuadratic Q R
      (fun i => L i (exteriorRotation Q g⁻¹ x))) sourceHaar := by
  apply Continuous.integrable_of_hasCompactSupport _ (isClosed_tsupport _).isCompact
  unfold occupationQuadratic occupationInner
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  apply continuous_const.mul
  apply continuous_finsetSum
  intro A hA
  exact (linearMap_rotation_coordinate_continuous Q (L i) x A).star.mul
    (linearMap_rotation_coordinate_continuous Q (L j) x A)

theorem physical_fourBody_haar_transfer (Q D : ℕ) (hQ : 25 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    -(24 * fourBodyRho D Q * sourceFockEnergy Q x) ≤
      (2*Q-2+1 : ℕ) * (∫ g, occupationQuadratic Q (finiteFourMiddle Q D)
        (fun i : Fin ((D+1)/2) => physicalFourCopyEnd Q (Certificate.copyLabel i) D
          (by omega) (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  have hw : Integrable (fun g : SourceSU2 => sourcePairWindow Q (exteriorRotation Q g⁻¹ x)) sourceHaar :=
    integrable_finsetSum _ (fun (p : ℕ) hp =>
      linearMap_rotation_norm_integrable Q (sourcePairEnd Q p) x)
  let L : Fin ((D+1)/2) → Module.End ℂ (Space Q) := fun i =>
    physicalFourCopyEnd Q (Certificate.copyLabel i) D (by omega)
  have hi := integral_mono ((hw.const_mul (fourBodyRho D Q)).neg)
    (occupationQuadratic_rotation_integrable Q (finiteFourMiddle Q D) L x)
    (fun g => source_fourBody_uniform_transfer Q D (by omega) hD₁ hD₂ (exteriorRotation Q g⁻¹ x))
  have hi := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ (2*Q-2+1 : ℕ))
  simp only [Pi.neg_apply] at hi
  rw [integral_neg,integral_const_mul] at hi
  have he : ((2*Q-2+1 : ℕ) : ℝ) *
      -(fourBodyRho D Q * (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar)) =
        -(24 * fourBodyRho D Q * sourceFockEnergy Q x) := by
    calc
      _ = -(fourBodyRho D Q * ((2*Q-2+1 : ℕ) *
        (∫ g, sourcePairWindow Q (exteriorRotation Q g⁻¹ x) ∂sourceHaar))) := by ring
      _ = _ := by rw [sourcePairWindow_haar Q hQ]; ring
  rwa [he] at hi

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TotalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators

theorem physical_fourBody_total_haar_transfer_oai (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    -(averagedFourTransferError Q * sourceFockEnergy Q x) ≤
      ∑ d : Fin 23, (2*Q-2+1 : ℕ) * (∫ g, occupationQuadratic Q (finiteFourMiddle Q (d.val+1))
        (fun i : Fin ((d.val+2)/2) => physicalFourCopyEnd Q
          (Certificate.copyLabel (D := d.val+1) i) (d.val+1) (by omega)
          (exteriorRotation Q g⁻¹ x)) ∂sourceHaar) := by
  have hs : (∑ d : Fin 23, fourBodyRho (d.val+1) Q) ≤ uniformFourBodyRho Q := by
    rw [Fin.sum_univ_eq_sum_range (fun d => fourBodyRho (d+1) Q) 23]
    unfold uniformFourBodyRho
    rw [Finset.sum_range_succ' (fun D => fourBodyRho D Q) 23]
    exact le_add_of_nonneg_right (fourBodyRho_nonneg 0 Q)
  have hE : 0 ≤ sourceFockEnergy Q x :=
    Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  calc
    _ ≤ -(24 * (∑ d : Fin 23, fourBodyRho (d.val+1) Q) * sourceFockEnergy Q x) :=
      neg_le_neg (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hE)
    _ = ∑ d : Fin 23, -(24 * fourBodyRho (d.val+1) Q * sourceFockEnergy Q x) := by
      rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_neg_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact physical_fourBody_haar_transfer Q (d.val+1) hQ (by omega) (by omega) x

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_fourBody_total_haar_transfer_oai := @OAI.Laughlin.Fock.physical_fourBody_total_haar_transfer_oai

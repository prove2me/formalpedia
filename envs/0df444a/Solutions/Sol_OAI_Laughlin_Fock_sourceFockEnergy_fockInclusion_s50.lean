-- Prove2me | solution 1 for OAI.Laughlin.Fock.sourceFockEnergy_fockInclusion_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T17:56:00.98802+00:00
-- url     : https://prove2.me/submissions/3c6c835c-1fc3-44fb-9444-036a6bc02392

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L008
import Definitions.Def_OAIQ050L012
import Theorems.Thm_OAI_Laughlin_Fock_fockInclusion_normSq_s50
import Theorems.Thm_OAI_Laughlin_Fock_pair_annihilate_high_degree_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_Conjugation
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_ModeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem contraction_map_between (L Q : ℕ) (f : Orbital L →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space L) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul,ExteriorAlgebra.map_apply_ι,CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply,map_sub,map_smul,hx]

theorem fockInclusion_annihilate (L Q : ℕ) (h : L ≤ Q) (i : Fin (L+1)) (x : Space L) :
    annihilate (Fin.castLE (Nat.add_le_add_right h 1) i) (fockInclusion L Q h x) =
      fockInclusion L Q h (annihilate i x) := by
  unfold annihilate fockInclusion
  rw [contraction_map_between]
  have hp : (LinearMap.proj (Fin.castLE (Nat.add_le_add_right h 1) i)).comp
      (modeInclusion L Q h) = LinearMap.proj i := by
    apply LinearMap.ext
    intro v
    change (if hj : i.val ≤ L then v ⟨i.val,by omega⟩ else 0) = v i
    rw [dite_eq_left (show i.val ≤ L by omega)]
  rw [hp]

theorem fockInclusion_annihilate_high (L Q : ℕ) (h : L ≤ Q) (i : Fin (Q+1))
    (hi : L < i.val) (x : Space L) :
    annihilate i (fockInclusion L Q h x) = 0 := by
  unfold annihilate fockInclusion
  rw [contraction_map_between]
  have he : (LinearMap.proj i).comp (modeInclusion L Q h) = 0 := by
    ext v
    simp [modeInclusion,show ¬i.val ≤ L by omega]
  rw [he]
  simp

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

theorem sphereCoefficient_eq (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (i j : Fin (Q+1)) :
    sphereCoefficient Q p i.val j.val = ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [sphereCoefficient,pairCoefficient_conjugation Q p hQ hp]

end Laughlin.Planar

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Planar_DegreeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_fin_castLE_of_high_zero {R : Type*} [AddCommMonoid R]
    (L Q : ℕ) (h : L ≤ Q) (f : Fin (Q+1) → R)
    (hf : ∀ i, L < i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin (L+1), f (Fin.castLE (Nat.add_le_add_right h 1) i) := by
  classical
  let e := Fin.castLEEmb (Nat.add_le_add_right h 1)
  have hz : ∑ i ∈ Finset.univ.map e, f i = ∑ i : Fin (Q+1), f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hin
    apply hf
    by_contra hh
    have hiL : i.val ≤ L := by omega
    apply hin
    exact Finset.mem_map.mpr ⟨⟨i.val,by omega⟩,Finset.mem_univ _,Fin.ext rfl⟩
  rw [← hz,Finset.sum_map]
  rfl

theorem pairEnd_fockInclusion (L Q : ℕ) (h : L ≤ Q)
    (c : Fin (Q+1) → Fin (Q+1) → ℂ) (x : Space L) :
    pairEnd Q c (fockInclusion L Q h x) =
      fockInclusion L Q h (pairEnd L
        (fun i j => c (Fin.castLE (Nat.add_le_add_right h 1) i)
          (Fin.castLE (Nat.add_le_add_right h 1) j)) x) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul]
  rw [sum_fin_castLE_of_high_zero L Q h _ (by
    intro i hi
    simp [fockInclusion_annihilate_high L Q h i hi])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_fin_castLE_of_high_zero L Q h _ (by
    intro j hj
    rw [fockInclusion_annihilate]
    simp [fockInclusion_annihilate_high L Q h j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fockInclusion_annihilate,fockInclusion_annihilate]

theorem pairEnd_high_degree (Q d p : ℕ) (x : Space Q) (hx : DegreeAtMost Q d x)
    (hp : d < p+1) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (hc : ∀ i j, i.val+j.val ≠ p+1 → c i j = 0) : pairEnd Q c x = 0 := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  by_cases he : i.val+j.val=p+1
  · rw [pair_annihilate_high_degree_s50 Q d x hx i j (by omega),smul_zero]
  · rw [hc i j he,zero_smul]

theorem sourcePairEnd_fockInclusion (L Q p : ℕ) (h : L ≤ Q)
    (hQ : 0 < Q) (hp : p ≤ 2*Q-2) (x : Space L) :
    sourcePairEnd Q p (fockInclusion L Q h x) =
      fockInclusion L Q h (restrictedSpherePairEnd L Q p x) := by
  unfold sourcePairEnd
  rw [pairEnd_fockInclusion]
  unfold restrictedSpherePairEnd
  congr 2
  congr 1
  funext i j
  exact (Planar.sphereCoefficient_eq Q p hQ hp
    (Fin.castLE (Nat.add_le_add_right h 1) i) (Fin.castLE (Nat.add_le_add_right h 1) j)).symm

theorem restrictedSpherePairEnd_high_degree (L Q d p : ℕ) (x : Space L)
    (hx : DegreeAtMost L d x) (hp : d < p+1) : restrictedSpherePairEnd L Q p x = 0 := by
  apply pairEnd_high_degree L d p x hx hp
  intro i j hij
  simp [Planar.sphereCoefficient,pairLimitCoefficient,hij]

theorem sum_range_eq_short {M : Type*} [AddCommMonoid M] (n m : ℕ) (hnm : n ≤ m)
    (f : ℕ → M) (hf : ∀ k, n ≤ k → k < m → f k = 0) :
    (∑ k ∈ Finset.range m, f k) = ∑ k ∈ Finset.range n, f k := by
  symm
  apply Finset.sum_subset (Finset.range_mono hnm)
  intro k hk hkn
  exact hf k (by simpa using hkn) (Finset.mem_range.mp hk)

theorem sourceFockEnergy_fockInclusion_s50_oai (L Q : ℕ) (hQ : L+2 ≤ Q)
    (x : Space L) (hx : DegreeAtMost L L x) :
    sourceFockEnergy Q (fockInclusion L Q (by omega) x) = restrictedSphereEnergy L Q x := by
  have h : L ≤ Q := by omega
  unfold sourceFockEnergy restrictedSphereEnergy
  rw [sum_range_eq_short L (2*Q-1) (by omega) _ (by
    intro p hp hpQ
    rw [sourcePairEnd_fockInclusion L Q p h (by omega) (by omega),
      restrictedSpherePairEnd_high_degree L Q L p x hx (by omega),map_zero]
    simp [occupationNormSq])]
  rw [sum_range_eq_short L (2*L+1) (by omega) _ (by
    intro p hp hpL
    rw [restrictedSpherePairEnd_high_degree L Q L p x hx (by omega)]
    simp [occupationNormSq])]
  apply Finset.sum_congr rfl
  intro p hp
  have hpL := Finset.mem_range.mp hp
  rw [sourcePairEnd_fockInclusion L Q p h (by omega) (by omega),fockInclusion_normSq_s50]

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.sourceFockEnergy_fockInclusion_s50_oai := @OAI.Laughlin.Fock.sourceFockEnergy_fockInclusion_s50_oai

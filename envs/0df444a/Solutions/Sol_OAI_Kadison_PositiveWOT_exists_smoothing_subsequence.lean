-- Prove2me | solution 1 for OAI.Kadison.PositiveWOT.exists_smoothing_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:07:31.351845+00:00
-- url     : https://prove2.me/submissions/6937adcc-8a3b-4c6d-b6f6-1c7e26e41061

import Mathlib
import Theorems.Thm_OAI_Kadison_PositiveWOT_exists_injective_inverse_limit

section
-- module Solutions.OAIQ039_CM.Commutator_PositiveWOT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma nonneg_limit {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,0≤T i) : 0≤W := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hh : 0 ≤ inner ℂ (W x) x := ge_of_tendsto (ht x x) (hp.mono fun i hi =>
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hi).inner_nonneg_left x)
  exact ⟨Complex.ext (by simp) (by simpa using hh.2),hh.1⟩

lemma limit_le {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W A : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,T i≤A) : W≤A := by
  apply sub_nonneg.mp
  refine nonneg_limit (T:=fun i => A-T i) ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
  intro x y
  simpa only [sub_apply,inner_sub_left] using
    ((tendsto_const_nhds (x:=inner ℂ (A x) y)).sub (ht x y))

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeightedSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter Finset

open scoped Topology

namespace Kadison.PositiveWOT

theorem exists_weighted_subsequence (q : ℕ → ℕ → ℝ)
    (hq : ∀ n j,0≤q n j) (ht : ∀ j,Tendsto (fun n => q n j) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ,StrictMono u ∧ ∀ j,∃ C : ℝ,∀ N,
      ∑ k∈range N,((k:ℝ)+1)*q (u k) j≤C := by
  have hev (k : ℕ) : ∀ᶠ n in atTop,∀ j∈range (k+1),
      q n j≤(1/2:ℝ)^k/((k:ℝ)+1) := by
    apply (eventually_all_finset (range (k+1))).mpr
    intro j _
    exact ((ht j).eventually_lt_const (by positivity : (0:ℝ)<(1/2:ℝ)^k/((k:ℝ)+1))).mono
      fun _ h => h.le
  obtain ⟨u,hu,huq⟩ := Tendsto.subseq_mem (V:=fun k => {n | ∀ j∈range (k+1),
    q n j≤(1/2:ℝ)^k/((k:ℝ)+1)}) hev (tendsto_id (α:=ℕ) : Tendsto id atTop atTop)
  refine ⟨u,hu,?_⟩
  intro j
  let z (k : ℕ) : ℝ := ((k:ℝ)+1)*q (u k) j
  have hz (k : ℕ) : 0≤z k := mul_nonneg (by positivity) (hq _ _)
  have hsmall (k : ℕ) (hjk : j≤k) : z k≤(1/2:ℝ)^k := by
    have h := huq k j (mem_range.mpr (by omega))
    dsimp [z]
    simpa only [mul_comm,id_eq] using (le_div_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mp h
  refine ⟨(∑ k∈range j,z k)+2,?_⟩
  intro N
  change (∑ k∈range N,z k)≤_
  rcases le_total N j with hNj|hjN
  · have hh : (∑ k∈range N,z k)≤∑ k∈range j,z k :=
      sum_le_sum_of_subset_of_nonneg (range_mono hNj) (fun k _ _ => hz k)
    linarith
  · rw [←sum_range_add_sum_Ico z hjN]
    refine add_le_add le_rfl ?_
    calc
      (∑ k∈Ico j N,z k)≤∑ k∈Ico j N,(1/2:ℝ)^k :=
        sum_le_sum (fun k hk => hsmall k (mem_Ico.mp hk).1)
      _ ≤ ∑ k∈range N,(1/2:ℝ)^k := sum_le_sum_of_subset_of_nonneg
        (by intro k hk; exact mem_range.mpr (mem_Ico.mp hk).2) (by intros; positivity)
      _ ≤ 2 := sum_geometric_two_le N

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SmoothingSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter Finset

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sandwich_nonneg {A B : H →L[ℂ] H} (hA : 0≤A) (hB : IsSelfAdjoint B) : 0≤B*A*B := by
  simpa using hB.conjugate_le_conjugate hA

lemma inverse_sandwich_le (S : H →L[ℂ] H) (hS : 1≤S) {A : H →L[ℂ] H} (hA : A≤S) :
    Ring.inverse S*A*Ring.inverse S≤Ring.inverse S := by
  let U := (CStarAlgebra.isUnit_of_le 1 hS).unit
  have hu : (U:H →L[ℂ] H)=S := IsUnit.unit_spec _
  have hi : Ring.inverse S=(↑U⁻¹:H →L[ℂ] H) := by rw [←hu,Ring.inverse_unit]
  have hpos : 0≤(↑U⁻¹:H →L[ℂ] H) := CFC.inv_nonneg_of_nonneg U (by rw [hu]; exact zero_le_one.trans hS)
  rw [hi]
  have hh := (IsSelfAdjoint.of_nonneg hpos).conjugate_le_conjugate hA
  rw [←hu,Units.inv_mul,one_mul] at hh
  exact hh

lemma sandwich_inner {A B : H →L[ℂ] H} (hb : IsSelfAdjoint B) (x y : H) :
    inner ℂ ((B*A*B) x) y=inner ℂ (A (B x)) (B y) := by
  have hh := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hb (A (B x)) y
  exact hh

lemma sandwich_strong_limit {P : ℕ → H →L[ℂ] H} {B A : H →L[ℂ] H}
    (hP : ∀ n,IsSelfAdjoint (P n)) (hB : IsSelfAdjoint B)
    (ht : ∀ x,Tendsto (fun n => P n x) atTop (𝓝 (B x))) (x y : H) :
    Tendsto (fun n => inner ℂ ((P n*A*P n) x) y) atTop (𝓝 (inner ℂ ((B*A*B) x) y)) := by
  simp only [sandwich_inner (hP _),sandwich_inner hB]
  exact (A.continuous.tendsto _ |>.comp (ht x)).inner (ht y)

theorem exists_smoothing_subsequence_oai [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (A : ℕ → H →L[ℂ] H) (hAM : ∀ n,A n∈M)
    (hA : ∀ n,0≤A n) (ht : ∀ x,Tendsto (fun n => A n x) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ,StrictMono u ∧ ∃ B : H →L[ℂ] H,
      B∈M ∧ 0≤B ∧ B≤1 ∧ Function.Injective B ∧
      ∀ k,‖B*A (u k)*B‖≤1/((k:ℝ)+1) := by
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq H
  let q (n j : ℕ) := (inner ℂ (A n (v j)) (v j)).re
  have hq (n j : ℕ) : 0≤q n j :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (hA n)).re_inner_nonneg_left _
  have hqt (j : ℕ) : Tendsto (fun n => q n j) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => (inner ℂ (A n (v j)) (v j)).re) atTop (𝓝 ((inner ℂ (0:H) (v j)).re)) :=
      Complex.continuous_re.tendsto _ |>.comp ((ht (v j)).inner (tendsto_const_nhds (x:=v j)))
    simpa only [q,Function.comp_apply,inner_zero_left,Complex.zero_re] using hh
  obtain ⟨u,hu,hbounded⟩ := exists_weighted_subsequence q hq hqt
  let S (N : ℕ) : H →L[ℂ] H := 1+∑ k∈range N,((k:ℝ)+1) • A (u k)
  have hp (k : ℕ) : 0≤((k:ℝ)+1) • A (u k) := smul_nonneg (by positivity) (hA _)
  have hS1 (N : ℕ) : 1≤S N := le_add_of_nonneg_right (sum_nonneg fun k _ => hp k)
  have hSM (N : ℕ) : S N∈M := M.add_mem M.one_mem
    (M.sum_mem fun k _ => by
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
      change (Complex.ofReal ((k:ℝ)+1)) • A (u k)∈M
      exact M.toStarSubalgebra.smul_mem (hAM (u k)) (Complex.ofReal ((k:ℝ)+1)))
  have hSmono : Monotone S := by
    intro n m hnm
    exact add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (range_mono hnm) (fun k _ _ => hp k))
  have hform (N j : ℕ) : (inner ℂ (S N (v j)) (v j)).re=
      (inner ℂ (v j) (v j)).re+∑ k∈range N,((k:ℝ)+1)*q (u k) j := by
    have hsm (r : ℝ) (T : H →L[ℂ] H) :
        inner ℂ ((r • T) (v j)) (v j)=r • inner ℂ (T (v j)) (v j) := by
      rw [smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ),inner_smul_real_left]
    simp only [S,add_apply,one_apply_eq_self,
      _root_.sum_apply,inner_add_left,sum_inner,hsm,
      Complex.add_re,Complex.re_sum,Complex.smul_re,smul_eq_mul,q]
  have hSb (j : ℕ) : ∃ C : ℝ,∀ N,(inner ℂ (S N (v j)) (v j)).re≤C := by
    obtain ⟨C,hC⟩ := hbounded j
    exact ⟨(inner ℂ (v j) (v j)).re+C,fun N => by rw [hform]; exact add_le_add le_rfl (hC N)⟩
  obtain ⟨B,hBM,hBp,hB1,hBi,hBSl,hBS⟩ := exists_injective_inverse_limit M S hSM hS1 hSmono v hv hSb
  refine ⟨u,hu,B,hBM,hBp,hB1,hBi,?_⟩
  intro k
  have hBB : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg hBp
  have hSipos (n : ℕ) : 0≤Ring.inverse (S n) := by
    let U := (CStarAlgebra.isUnit_of_le 1 (hS1 n)).unit
    have hu : (U:H →L[ℂ] H)=S n := IsUnit.unit_spec _
    rw [←hu,Ring.inverse_unit]
    exact CFC.inv_nonneg_of_nonneg U (by rw [hu]; exact zero_le_one.trans (hS1 n))
  have hSi1 (n : ℕ) : Ring.inverse (S n)≤1 := by
    let U := (CStarAlgebra.isUnit_of_le 1 (hS1 n)).unit
    have hu : (U:H →L[ℂ] H)=S n := IsUnit.unit_spec _
    rw [←hu,Ring.inverse_unit]
    exact CStarAlgebra.inv_le_one (by change 1≤(U:H →L[ℂ] H); rw [hu]; exact hS1 n)
  have hsand : B*(((k:ℝ)+1) • A (u k))*B≤1 := by
    apply limit_le (sandwich_strong_limit (fun n => IsSelfAdjoint.of_nonneg (hSipos n)) hBB hBS)
    filter_upwards [eventually_ge_atTop (k+1)] with n hn
    have hle : ((k:ℝ)+1) • A (u k)≤S n := by
      have hh : ((k:ℝ)+1) • A (u k)≤∑ j∈range n,((j:ℝ)+1) • A (u j) :=
        single_le_sum (fun j _ => hp j) (mem_range.mpr (by omega))
      exact hh.trans (le_add_of_nonneg_left zero_le_one)
    exact (inverse_sandwich_le (S n) (hS1 n) hle).trans (hSi1 n)
  rw [mul_smul_comm,smul_mul_assoc] at hsand
  have hnorm := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (smul_nonneg (by positivity : (0:ℝ)≤(k:ℝ)+1) (sandwich_nonneg (hA _) hBB))).mpr hsand
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤(k:ℝ)+1)] at hnorm
  exact (le_div_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr (by simpa only [mul_comm] using hnorm)

end Kadison.PositiveWOT

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PositiveWOT.exists_smoothing_subsequence_oai.{u_1} := @OAI.Kadison.PositiveWOT.exists_smoothing_subsequence_oai.{u_1}

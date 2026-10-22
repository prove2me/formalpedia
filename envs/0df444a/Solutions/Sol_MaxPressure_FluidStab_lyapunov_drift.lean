-- Prove2me | solution 1 for MaxPressure.FluidStab.lyapunov_drift
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:51:50.96518+00:00
-- url     : https://prove2.me/submissions/c61bd76d-9b8d-4b2f-8b59-dea4cce0e0d5

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

set_option autoImplicit false
open MaxPressure.FluidStab Matrix

namespace HHM
variable {I J K : ℕ}

lemma alloc_convex (N : Network I J K) : Convex ℝ (allocSet N) := by
  intro a ha b hb s t hs ht hst
  obtain ⟨ha0, ha1, ha2⟩ := ha
  obtain ⟨hb0, hb1, hb2⟩ := hb
  have hlin : ∀ k, ∑ j, N.A k j * (s • a + t • b) j = s * ∑ j, N.A k j * a j + t * ∑ j, N.A k j * b j := by
    intro k
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun j => ?_, fun k => ?_, fun k hk => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (ha0 j)) (mul_nonneg ht (hb0 j))
  · rw [hlin]
    nlinarith [ha1 k, hb1 k]
  · rw [hlin, ha2 k hk, hb2 k hk]
    linarith

lemma alloc_compact (N : Network I J K) (hN : N.Standing) : IsCompact (allocSet N) := by
  obtain ⟨hAB, hBB, hne, hio, hAk, hproc, hex, hinput, hm, hP, hP00⟩ := hN
  have hclosed : IsClosed (allocSet N) := by
    have : allocSet N = (⋂ j, {a : Fin J → ℝ | 0 ≤ a j}) ∩ ((⋂ k, {a : Fin J → ℝ | ∑ j, N.A k j * a j ≤ 1}) ∩
        (⋂ k, ⋂ (_ : N.inputProc k), {a : Fin J → ℝ | ∑ j, N.A k j * a j = 1})) := by
      ext a
      simp only [allocSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [this]
    refine IsClosed.inter (isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))) (IsClosed.inter
      (isClosed_iInter (fun k => isClosed_le (by fun_prop) continuous_const))
      (isClosed_iInter (fun k => isClosed_iInter (fun _ => isClosed_eq (by fun_prop) continuous_const))))
  have hsub : allocSet N ⊆ Set.pi Set.univ (fun _ : Fin J => Set.Icc (0 : ℝ) 1) := by
    intro a ha j _
    obtain ⟨ha0, ha1, ha2⟩ := ha
    obtain ⟨k, hk⟩ := hAk j
    refine ⟨ha0 j, ?_⟩
    have h1 := ha1 k
    have h2 : N.A k j * a j ≤ ∑ j', N.A k j' * a j' :=
      Finset.single_le_sum (f := fun j' => N.A k j' * a j')
        (fun j' _ => mul_nonneg (by rcases hAB k j' with h | h <;> rw [h] <;> norm_num) (ha0 j'))
        (Finset.mem_univ j)
    rw [hk, one_mul] at h2
    linarith
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hsub

lemma press_max (N : Network I J K) (hN : N.Standing) (z : Fin I → ℝ) (P0 : ℝ)
    (h : ∀ a ∈ extremeAllocs N, pressure N a z ≤ P0) :
    ∀ a ∈ allocSet N, pressure N a z ≤ P0 := by
  have hlinmap : IsLinearMap ℝ (fun a : Fin J → ℝ => pressure N a z) := by
    constructor
    · intro a b
      simp [pressure, mulVec_add, dotProduct_add]
    · intro c a
      simp [pressure, mulVec_smul, dotProduct_smul]
  have hHconv : Convex ℝ {a : Fin J → ℝ | pressure N a z ≤ P0} := convex_halfSpace_le hlinmap P0
  have hHclosed : IsClosed {a : Fin J → ℝ | pressure N a z ≤ P0} := by
    refine isClosed_le ?_ continuous_const
    simp only [pressure, dotProduct, mulVec]
    fun_prop
  have hKM := closure_convexHull_extremePoints (alloc_compact N hN) (alloc_convex N)
  have hsub : extremeAllocs N ⊆ {a : Fin J → ℝ | pressure N a z ≤ P0} := fun a ha => h a ha
  have : closure (convexHull ℝ (extremeAllocs N)) ⊆ {a : Fin J → ℝ | pressure N a z ≤ P0} :=
    closure_minimal (convexHull_min hsub hHconv) hHclosed
  intro a ha
  have ha' : a ∈ closure (convexHull ℝ (extremeAllocs N)) := by
    unfold extremeAllocs
    rw [hKM]; exact ha
  exact this ha'

lemma plb {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (t : ℝ) (ht : IsRegular Zb Tb t) :
    pressure N xs (Zb t) ≤ pressure N (deriv Tb t) (Zb t) ∧
    ε * ∑ i, Zb t i ≤ pressure N xs (Zb t) ∧
    ε * Real.sqrt (∑ i, Zb t i ^ 2) ≤ ε * ∑ i, Zb t i := by
  have hz : ∀ i, 0 ≤ Zb t i := fun i => hsol.2.1 t ht.1.le i
  refine ⟨?_, ?_, ?_⟩
  · have hg := hmp t ht
    exact HHM.press_max N hN (Zb t) _ (fun a ha => hg.2 ⟨a, ha, rfl⟩) xs hxs
  · unfold pressure
    simp only [dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hR i) (hz i)
  · refine mul_le_mul_of_nonneg_left ?_ hε.le
    rw [Real.sqrt_le_iff]
    refine ⟨Finset.sum_nonneg (fun i _ => hz i), ?_⟩
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc Zb t i ^ 2 = Zb t i * Zb t i := sq _
      _ ≤ ∑ j, Zb t i * Zb t j :=
        Finset.single_le_sum (f := fun j => Zb t i * Zb t j)
          (fun j _ => mul_nonneg (hz i) (hz j)) (Finset.mem_univ i)

end HHM

theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (t : ℝ) (ht : IsRegular Zb Tb t) :
    HasDerivAt (fun s => ∑ i, Zb s i ^ 2) (2 * (deriv Zb t ⬝ᵥ Zb t)) t ∧
    2 * (deriv Zb t ⬝ᵥ Zb t) = -2 * pressure N (deriv Tb t) (Zb t) ∧
    -2 * pressure N (deriv Tb t) (Zb t) ≤ -2 * ε * Real.sqrt (∑ i, Zb t i ^ 2) := by
  obtain ⟨htpos, hZd, hTd⟩ := ht
  have hZ : HasDerivAt Zb (deriv Zb t) t := hZd.hasDerivAt
  have hT : HasDerivAt Tb (deriv Tb t) t := hTd.hasDerivAt
  have hZi : ∀ i, HasDerivAt (fun s => Zb s i) (deriv Zb t i) t := fun i => hasDerivAt_pi.mp hZ i
  have hTj : ∀ j, HasDerivAt (fun s => Tb s j) (deriv Tb t j) t := fun j => hasDerivAt_pi.mp hT j
  refine ⟨?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun s => ∑ i, Zb s i ^ 2)
        (∑ i, ((2 : ℕ) : ℝ) * Zb t i ^ (2 - 1) * deriv Zb t i) t :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hZi i).fun_pow 2)
    convert h1 using 1
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    ring
  · -- derivative of Z from the fluid model equation (14)
    have hder : ∀ i : Fin I, deriv Zb t i
        = ∑ i' : Fin (I + 1), ∑ j : Fin J, deriv Tb t j * μ N j * N.B j i' * N.P j i' i.succ
          - ∑ j : Fin J, deriv Tb t j * μ N j * N.B j i.succ := by
      intro i
      have hg : HasDerivAt (fun s => Zb 0 i
          + ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * μ N j * N.B j i' * N.P j i' i.succ
          - ∑ j : Fin J, Tb s j * μ N j * N.B j i.succ)
          (0 + ∑ i' : Fin (I + 1), ∑ j : Fin J, deriv Tb t j * μ N j * N.B j i' * N.P j i' i.succ
          - ∑ j : Fin J, deriv Tb t j * μ N j * N.B j i.succ) t := by
        refine HasDerivAt.sub (HasDerivAt.add (hasDerivAt_const t (Zb 0 i)) ?_) ?_
        · refine HasDerivAt.fun_sum (u := Finset.univ) (fun i' _ => ?_)
          exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (((hTj j).mul_const (μ N j)).mul_const (N.B j i')).mul_const (N.P j i' i.succ))
        · exact HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hTj j).mul_const (μ N j)).mul_const (N.B j i.succ))
      have heq : (fun s => Zb s i) =ᶠ[nhds t] (fun s => Zb 0 i
          + ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb s j * μ N j * N.B j i' * N.P j i' i.succ
          - ∑ j : Fin J, Tb s j * μ N j * N.B j i.succ) := by
        filter_upwards [Ioi_mem_nhds htpos] with s hs
        exact hsol.1 s (le_of_lt hs) i
      have := (hg.congr_of_eventuallyEq heq)
      rw [(hZi i).unique this]
      ring
    have hderR : deriv Zb t = -(R N *ᵥ deriv Tb t) := by
      funext i
      rw [hder i]
      simp only [Pi.neg_apply, mulVec, dotProduct, R, μ]
      have : ∀ j : Fin J, 1 / N.m j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ) * deriv Tb t j
          = deriv Tb t j * (1 / N.m j) * N.B j i.succ
            - ∑ i' : Fin (I + 1), deriv Tb t j * (1 / N.m j) * N.B j i' * N.P j i' i.succ := by
        intro j
        rw [mul_sub, sub_mul]
        congr 1
        · ring
        · rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i' _ => ?_)
          ring
      simp_rw [this]
      rw [Finset.sum_sub_distrib, Finset.sum_comm]
      ring
    rw [hderR]
    unfold pressure
    rw [neg_dotProduct, dotProduct_comm]
    ring
  · have hp := HHM.plb N hN Zb Tb hsol hmp xs hxs ε hε hR t ⟨htpos, hZd, hTd⟩
    nlinarith [hp.1, hp.2.1, hp.2.2]

-- Prove2me | solution 1 for MFGPlanning.Penalized.proposition_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:38:44.136976+00:00
-- url     : https://prove2.me/submissions/faad6730-722d-40e0-bdd9-8453703824b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme
import Definitions.Def_MFGPlanning_Penalized_Duality
import Theorems.Thm_MFGPlanning_Penalized_proposition_1
import Theorems.Thm_MFGPlanning_Penalized_proposition_3
import Theorems.Thm_MFGPlanning_Penalized_theorem_2
set_option autoImplicit false

namespace MFGPlanning.Penalized.Prop4Aux

open MFGPlanning.Penalized Filter Topology

theorem t_lap (d : Data) {u : ℕ → Pt d → ℝ} {ub : Pt d → ℝ}
    (h : ∀ p, Tendsto (fun k => u k p) atTop (𝓝 (ub p))) (p : Pt d) :
    Tendsto (fun k => lap d (u k) p) atTop (𝓝 (lap d ub p)) := by
  unfold lap
  exact tendsto_const_nhds.mul ((((((h p).const_mul 4).sub (h _)).sub (h _)).sub (h _)).sub (h _))

theorem t_Dh (d : Data) {u : ℕ → Pt d → ℝ} {ub : Pt d → ℝ}
    (h : ∀ p, Tendsto (fun k => u k p) atTop (𝓝 (ub p))) (p : Pt d) :
    Tendsto (fun k => Dh d (u k) p) atTop (𝓝 (Dh d ub p)) := by
  have h1 : ∀ q : Pt d, Tendsto (fun k => D1 d (u k) q) atTop (𝓝 (D1 d ub q)) := fun q => by
    unfold D1; exact ((h _).sub (h _)).div_const _
  have h2 : ∀ q : Pt d, Tendsto (fun k => D2 d (u k) q) atTop (𝓝 (D2 d ub q)) := fun q => by
    unfold D2; exact ((h _).sub (h _)).div_const _
  rw [tendsto_pi_nhds]
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)))) i
  · simp only [Dh, Matrix.cons_val_zero]; exact h1 p
  · simp only [Dh, Matrix.cons_val_succ, Matrix.cons_val_zero]; exact h1 _
  · simp only [Dh, Matrix.cons_val_succ, Matrix.cons_val_zero]; exact h2 p
  · simp only [Dh, Matrix.cons_val_succ, Matrix.cons_val_zero]; exact h2 _

theorem dg_cont (d : Data) (hG3 : G3 d) (p : Pt d) (i : Fin 4) :
    Continuous (fun q => dg d p q i) := by
  unfold dg
  exact ((hG3 p).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem t_B (d : Data) (hG3 : G3 d) {u m : ℕ → Pt d → ℝ} {ub mb : Pt d → ℝ}
    (hu : ∀ p, Tendsto (fun k => u k p) atTop (𝓝 (ub p)))
    (hm : ∀ p, Tendsto (fun k => m k p) atTop (𝓝 (mb p))) (p : Pt d) :
    Tendsto (fun k => B d (u k) (m k) p) atTop (𝓝 (B d ub mb p)) := by
  have ht : ∀ (q : Pt d) (i : Fin 4), Tendsto (fun k => m k q * dg d q (Dh d (u k) q) i) atTop
      (𝓝 (mb q * dg d q (Dh d ub q) i)) :=
    fun q i => (hm q).mul (((dg_cont d hG3 q i).tendsto _).comp (t_Dh d hu q))
  simp only [B]
  exact tendsto_const_nhds.mul
    (((((ht p 0).sub (ht _ 0)).add (ht _ 1)).sub (ht p 1)).add
      ((((ht p 2).sub (ht _ 2)).add (ht _ 3)).sub (ht p 3)))

theorem inK_bound (d : Data) (m : Pt d → ℝ) (hm : InK d m) (p : Pt d) :
    0 ≤ m p ∧ m p ≤ (d.Nh : ℝ) ^ 2 := by
  refine ⟨hm.2 p, ?_⟩
  have hN : (d.Nh : ℝ) ≠ 0 := Nat.cast_ne_zero.2 d.hNh.ne'
  have hs : ∑ q, m q = (d.Nh : ℝ) ^ 2 := by
    have := hm.1
    rw [Data.h, inv_pow, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hN), mul_one] at this
    exact this
  rw [← hs]
  exact Finset.single_le_sum (fun q _ => hm.2 q) (Finset.mem_univ p)

/-- Penalized solutions have `0 ≤ M ≤ Nh²` at every level. -/
theorem M_bound (d : Data) (hmT : InK d d.mT) (ε : ℝ) (U M : Fin (d.NT + 1) → Pt d → ℝ)
    (hsol : IsPenalizedSol d ε U M) (n : Fin (d.NT + 1)) (p : Pt d) :
    0 ≤ M n p ∧ M n p ≤ (d.Nh : ℝ) ^ 2 := by
  induction n using Fin.lastCases with
  | last => rw [hsol.2.2.2.2]; exact inK_bound d _ hmT p
  | cast i => exact inK_bound d _ (hsol.2.2.1 i) p

/-- Limit passage: limits of penalized solutions with `ε → 0` are normalized planning solutions. -/
theorem limit_sol (d : Data) (hG3 : G3 d) (hW : HypW d) (hm0 : InK d d.m0) (hmT : InK d d.mT)
    (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ) (Ubar Mbar : Fin (d.NT + 1) → Pt d → ℝ)
    (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hsol : ∀ k, IsPenalizedSol d (ε k) (U k) (M k))
    (hU : Tendsto U atTop (𝓝 Ubar)) (hM : Tendsto M atTop (𝓝 Mbar)) :
    IsPlanningSol d Ubar Mbar ∧ ∑ p, Ubar 0 p = 0 := by
  have tU : ∀ n p, Tendsto (fun k => U k n p) atTop (𝓝 (Ubar n p)) :=
    fun n p => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hU n) p
  have tM : ∀ n p, Tendsto (fun k => M k n p) atTop (𝓝 (Mbar n p)) :=
    fun n p => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hM n) p
  have hV : Continuous d.V := hW.1.continuous_deriv (by norm_num)
  have e0 : (⟨0, d.hNT⟩ : Fin d.NT).castSucc = 0 := Fin.ext (by simp)
  have h0 : ∀ k, InK d (M k 0) := fun k => by
    have := (hsol k).2.2.1 ⟨0, d.hNT⟩
    rwa [e0] at this
  have hh : d.h ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero (Nat.cast_ne_zero.2 d.hNh.ne'))
  have hS : ∀ k, ∑ p, U k 0 p = 0 := fun k => by
    have hs : ∑ p, M k 0 p = ∑ p, d.m0 p := mul_left_cancel₀ hh ((h0 k).1.trans hm0.1.symm)
    simp_rw [(hsol k).2.2.2.1, ← Finset.sum_div, Finset.sum_sub_distrib, hs, sub_self, zero_div]
  have hM0 : Mbar 0 = d.m0 := funext fun p => by
    have e : ∀ k, d.m0 p + ε k * U k 0 p = M k 0 p := fun k => by
      rw [(hsol k).2.2.2.1 p]
      have := (hε k).ne'
      field_simp
      ring
    have t1 : Tendsto (fun k => d.m0 p + ε k * U k 0 p) atTop (𝓝 (d.m0 p + 0 * Ubar 0 p)) :=
      tendsto_const_nhds.add (hε0.mul (tU 0 p))
    rw [zero_mul, add_zero] at t1
    exact tendsto_nhds_unique (tM 0 p) (t1.congr e)
  have hMT : Mbar (Fin.last d.NT) = d.mT := funext fun p =>
    tendsto_nhds_unique (tM _ p)
      ((tendsto_const_nhds (x := d.mT p)).congr fun k => by rw [(hsol k).2.2.2.2])
  have hK : ∀ n, InK d (Mbar n) := by
    intro n
    induction n using Fin.lastCases with
    | last => rw [hMT]; exact hmT
    | cast i =>
      constructor
      · have t : Tendsto (fun k => d.h ^ 2 * ∑ p, M k i.castSucc p) atTop
            (𝓝 (d.h ^ 2 * ∑ p, Mbar i.castSucc p)) :=
          tendsto_const_nhds.mul (tendsto_finsetSum _ fun p _ => tM _ p)
        exact tendsto_nhds_unique t
          ((tendsto_const_nhds (x := (1 : ℝ))).congr fun k => ((hsol k).2.2.1 i).1.symm)
      · intro p
        exact ge_of_tendsto' (tM _ p) fun k => ((hsol k).2.2.1 i).2 p
  refine ⟨⟨fun n p => ?_, fun n p => ?_, hK, hMT, hM0⟩, ?_⟩
  · have t1 : Tendsto (fun k => (U k n.succ p - U k n.castSucc p) / d.Δt
          - d.ν * lap d (U k n.succ) p + d.g p (Dh d (U k n.succ) p)) atTop
        (𝓝 ((Ubar n.succ p - Ubar n.castSucc p) / d.Δt
          - d.ν * lap d (Ubar n.succ) p + d.g p (Dh d (Ubar n.succ) p))) :=
      ((((tU _ p).sub (tU _ p)).div_const _).sub ((t_lap d (tU n.succ) p).const_mul _)).add
        (((hG3 p).continuous.tendsto _).comp (t_Dh d (tU n.succ) p))
    exact tendsto_nhds_unique t1
      (((hV.tendsto _).comp (tM _ p)).congr fun k => ((hsol k).1 n p).symm)
  · have t1 : Tendsto (fun k => (M k n.succ p - M k n.castSucc p) / d.Δt
          + d.ν * lap d (M k n.castSucc) p + B d (U k n.succ) (M k n.castSucc) p) atTop
        (𝓝 ((Mbar n.succ p - Mbar n.castSucc p) / d.Δt
          + d.ν * lap d (Mbar n.castSucc) p + B d (Ubar n.succ) (Mbar n.castSucc) p)) :=
      ((((tM _ p).sub (tM _ p)).div_const _).add ((t_lap d (tM n.castSucc) p).const_mul _)).add
        (t_B d hG3 (tU n.succ) (tM n.castSucc) p)
    exact tendsto_nhds_unique t1
      ((tendsto_const_nhds (x := (0 : ℝ))).congr fun k => ((hsol k).2.1 n p).symm)
  · exact tendsto_nhds_unique (tendsto_finsetSum _ fun p _ => tU 0 p)
      ((tendsto_const_nhds (x := (0 : ℝ))).congr fun k => (hS k).symm)


/-- The compactness/uniqueness assembly of Proposition 4 from Propositions 1, 3 and Theorem 2
(passed as hypotheses `hC2`, `hC1`, `hC3`). -/
theorem core (d : Data) (hG3 : G3 d) (hW : HypW d) (hm0 : InK d d.m0) (hmT : InK d d.mT)
    (hC1 : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ U M : Fin (d.NT + 1) → Pt d → ℝ, IsPenalizedSol d ε U M →
      ∀ (n : Fin (d.NT + 1)) (p : Pt d), |U n p| ≤ C)
    (hC2 : ∀ U M U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U M → IsPlanningSol d U' M' →
      M = M' ∧
        ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) → ∑ p, U 0 p = 0 → ∑ p, U' 0 p = 0 →
          U = U'))
    (hC3 : ∀ ε : ℝ, 0 < ε → ∃ U M : Fin (d.NT + 1) → Pt d → ℝ, IsPenalizedSol d ε U M) :
    (∀ (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ) (Mbar : Fin (d.NT + 1) → Pt d → ℝ),
      (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
      (∀ k, IsPenalizedSol d (ε k) (U k) (M k)) →
      (∀ n, InK d (Mbar n)) → Tendsto M atTop (𝓝 Mbar) →
      ∃ (Ubar : Fin (d.NT + 1) → Pt d → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (U ∘ φ) atTop (𝓝 Ubar) ∧ IsPlanningSol d Ubar Mbar) ∧
    ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) →
      ∃ Ubar Mbar : Fin (d.NT + 1) → Pt d → ℝ,
        (IsPlanningSol d Ubar Mbar ∧ ∑ p, Ubar 0 p = 0) ∧
        (∀ U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U' M' → ∑ p, U' 0 p = 0 →
          U' = Ubar ∧ M' = Mbar) ∧
        (∀ (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ),
          (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
          (∀ k, IsPenalizedSol d (ε k) (U k) (M k)) →
          Tendsto (fun k => (U k, M k)) atTop (𝓝 (Ubar, Mbar)))) := by
  obtain ⟨C, hC⟩ := hC1
  set S1 : Set (Fin (d.NT + 1) → Pt d → ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (-C) C with hS1
  set S2 : Set (Fin (d.NT + 1) → Pt d → ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 ((d.Nh : ℝ) ^ 2) with hS2
  have hS1c : IsCompact S1 := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hS2c : IsCompact S2 := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hKc : IsCompact (S1 ×ˢ S2) := hS1c.prod hS2c
  have mem1 : ∀ ε : ℝ, 0 < ε → ∀ U M, IsPenalizedSol d ε U M → U ∈ S1 := by
    intro ε hε U M hs
    simp only [hS1, Set.mem_univ_pi]
    intro n p
    exact abs_le.1 (hC ε hε U M hs n p)
  have mem2 : ∀ ε : ℝ, ∀ U M, IsPenalizedSol d ε U M → M ∈ S2 := by
    intro ε U M hs
    simp only [hS2, Set.mem_univ_pi]
    intro n p
    exact M_bound d hmT ε U M hs n p
  have hlim := limit_sol d hG3 hW hm0 hmT
  refine ⟨?_, fun hsc => ?_⟩
  · intro ε U M Mbar hε hε0 hsol _ hM
    obtain ⟨Ub, -, φ, hφ, hT⟩ := hS1c.tendsto_subseq (fun k => mem1 _ (hε k) _ _ (hsol k))
    exact ⟨Ub, φ, hφ, hT, (hlim (ε ∘ φ) (U ∘ φ) (M ∘ φ) Ub Mbar (fun k => hε _)
      (hε0.comp hφ.tendsto_atTop) (fun k => hsol _) hT (hM.comp hφ.tendsto_atTop)).1⟩
  · have hpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
    choose Us Ms hs using fun k : ℕ => hC3 (1 / ((k : ℝ) + 1)) (hpos k)
    obtain ⟨⟨Ub, Mb⟩, -, φ, hφ, hT⟩ := hKc.tendsto_subseq (x := fun k => (Us k, Ms k))
      (fun k => ⟨mem1 _ (hpos k) _ _ (hs k), mem2 _ _ _ (hs k)⟩)
    have hT1 : Tendsto (Us ∘ φ) atTop (𝓝 Ub) := (continuous_fst.tendsto _).comp hT
    have hT2 : Tendsto (Ms ∘ φ) atTop (𝓝 Mb) := (continuous_snd.tendsto _).comp hT
    obtain ⟨hP, hz0⟩ := hlim ((fun k : ℕ => 1 / ((k : ℝ) + 1)) ∘ φ) (Us ∘ φ) (Ms ∘ φ) Ub Mb
      (fun k => hpos _) (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      (fun k => hs _) hT1 hT2
    refine ⟨Ub, Mb, ⟨hP, hz0⟩, fun U' M' hP' hz1 => ?_, fun ε U M hε hε0 hsol => ?_⟩
    · obtain ⟨e1, e2⟩ := hC2 U' M' Ub Mb hP' hP
      exact ⟨e2 hsc hz1 hz0, e1⟩
    · apply tendsto_of_subseq_tendsto
      intro ns hns
      obtain ⟨⟨Ub', Mb'⟩, -, ψ, hψ, hT'⟩ := hKc.tendsto_subseq
        (x := fun k => (U (ns k), M (ns k)))
        (fun k => ⟨mem1 _ (hε _) _ _ (hsol _), mem2 _ _ _ (hsol _)⟩)
      have hnsψ : Tendsto (ns ∘ ψ) atTop atTop := hns.comp hψ.tendsto_atTop
      obtain ⟨hP'', hz2⟩ := hlim (ε ∘ ns ∘ ψ) (U ∘ ns ∘ ψ) (M ∘ ns ∘ ψ) Ub' Mb'
        (fun k => hε _) (hε0.comp hnsψ) (fun k => hsol _)
        ((continuous_fst.tendsto _).comp hT') ((continuous_snd.tendsto _).comp hT')
      obtain ⟨e1, e2⟩ := hC2 Ub' Mb' Ub Mb hP'' hP
      refine ⟨ψ, ?_⟩
      have e3 := e2 hsc hz2 hz0
      subst e1 e3
      exact hT'

end MFGPlanning.Penalized.Prop4Aux

open MFGPlanning.Penalized Filter Topology in
/-- Proposition 4 (hal-00465404v1, §3.2): reduction to Propositions 1 and 3 and Theorem 2. -/
theorem solution (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    (∀ (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ) (Mbar : Fin (d.NT + 1) → Pt d → ℝ),
      (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
      (∀ k, IsPenalizedSol d (ε k) (U k) (M k)) →
      (∀ n, InK d (Mbar n)) → Tendsto M atTop (𝓝 Mbar) →
      ∃ (Ubar : Fin (d.NT + 1) → Pt d → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
        Tendsto (U ∘ φ) atTop (𝓝 Ubar) ∧ IsPlanningSol d Ubar Mbar) ∧
    ((∀ p, StrictConvexOn ℝ Set.univ (d.g p)) →
      ∃ Ubar Mbar : Fin (d.NT + 1) → Pt d → ℝ,
        (IsPlanningSol d Ubar Mbar ∧ ∑ p, Ubar 0 p = 0) ∧
        (∀ U' M' : Fin (d.NT + 1) → Pt d → ℝ, IsPlanningSol d U' M' → ∑ p, U' 0 p = 0 →
          U' = Ubar ∧ M' = Mbar) ∧
        (∀ (ε : ℕ → ℝ) (U M : ℕ → Fin (d.NT + 1) → Pt d → ℝ),
          (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
          (∀ k, IsPenalizedSol d (ε k) (U k) (M k)) →
          Tendsto (fun k => (U k, M k)) atTop (𝓝 (Ubar, Mbar)))) :=
  MFGPlanning.Penalized.Prop4Aux.core d hG3 hW hm0 hmT
    (MFGPlanning.Penalized.proposition_3 d hG1 hG3 hG4 hG5 hW hm0 hmT hm0pos hνmT)
    (MFGPlanning.Penalized.proposition_1 d hG1 hG3 hG4 hG5 hW hm0 hmT hm0pos hνmT)
    (fun ε hε => by
      obtain ⟨M, -, -, -, U, -, hU⟩ :=
        MFGPlanning.Penalized.theorem_2 d hG1 hG3 hG4 hG5 hW hm0 hmT hm0pos hνmT ε hε
      exact ⟨U, M, hU⟩)

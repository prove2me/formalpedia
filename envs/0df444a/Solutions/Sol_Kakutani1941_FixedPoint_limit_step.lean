-- Prove2me | solution 1 for Kakutani1941.FixedPoint.limit_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:58:13.282538+00:00
-- url     : https://prove2.me/submissions/baf9ca9c-7ace-4c1b-818b-59f0f92fe37f

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
import Definitions.Def_Kakutani1941_FixedPoint_ApproximationData
set_option autoImplicit false
open Kakutani1941.FixedPoint

theorem solution {m r : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hScompact : IsCompact S)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (husc : IsUpperSemicontinuous S Φ)
    (happrox : ∀ ε : ℝ, 0 < ε → ApproximationData S Φ r ε) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by
  have H : ∀ n : ℕ, ∃ (x : EuclideanSpace ℝ (Fin m)) (xs ys : Fin (r + 1) → EuclideanSpace ℝ (Fin m))
      (w : Fin (r + 1) → ℝ), x ∈ S ∧ (∀ i, xs i ∈ S ∧ dist (xs i) x ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ i, ys i ∈ Φ (xs i)) ∧ w ∈ stdSimplex ℝ (Fin (r + 1)) ∧
      x = ∑ i, (w i) • xs i ∧ x = ∑ i, (w i) • ys i :=
    fun n => happrox _ (by positivity)
  choose x xs ys w hx hxs hys hw hx1 hx2 using H
  have ysS : ∀ n i, ys n i ∈ S := fun n i => (hΦ (xs n i) (hxs n i).1).1 (hys n i)
  have hKc : IsCompact (S ×ˢ (Set.pi Set.univ fun _ : Fin (r + 1) => S) ×ˢ
      (Set.pi Set.univ fun _ : Fin (r + 1) => S) ×ˢ stdSimplex ℝ (Fin (r + 1))) :=
    hScompact.prod ((isCompact_univ_pi fun _ => hScompact).prod
      ((isCompact_univ_pi fun _ => hScompact).prod (isCompact_stdSimplex ℝ (Fin (r + 1)))))
  have hmem : ∀ n, (x n, xs n, ys n, w n) ∈ (S ×ˢ (Set.pi Set.univ fun _ : Fin (r + 1) => S) ×ˢ
      (Set.pi Set.univ fun _ : Fin (r + 1) => S) ×ˢ stdSimplex ℝ (Fin (r + 1))) :=
    fun n => ⟨hx n, fun i _ => (hxs n i).1, fun i _ => ysS n i, hw n⟩
  obtain ⟨⟨x0, xs0, ys0, w0⟩, hK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hmem
  obtain ⟨hx0S, -, -, hw0⟩ := hK
  have l1 : Filter.Tendsto (fun n => x (φ n)) Filter.atTop (nhds x0) :=
    (continuous_fst.tendsto _).comp hlim
  have l2 : Filter.Tendsto (fun n => xs (φ n)) Filter.atTop (nhds xs0) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have l3 : Filter.Tendsto (fun n => ys (φ n)) Filter.atTop (nhds ys0) :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have l4 : Filter.Tendsto (fun n => w (φ n)) Filter.atTop (nhds w0) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have hε : Filter.Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hxs0 : ∀ i, xs0 i = x0 := by
    intro i
    have hi : Filter.Tendsto (fun n => xs (φ n) i) Filter.atTop (nhds (xs0 i)) :=
      tendsto_pi_nhds.1 l2 i
    have hd := hi.dist l1
    have : dist (xs0 i) x0 ≤ 0 :=
      le_of_tendsto_of_tendsto hd hε (Filter.Eventually.of_forall fun n => (hxs (φ n) i).2)
    exact dist_le_zero.mp this
  have hys0 : ∀ i, ys0 i ∈ Φ x0 := by
    intro i
    have hi : Filter.Tendsto (fun n => xs (φ n) i) Filter.atTop (nhds x0) := by
      rw [← hxs0 i]; exact tendsto_pi_nhds.1 l2 i
    exact husc (fun n => xs (φ n) i) (fun n => ys (φ n) i) x0 (ys0 i)
      (fun n => (hxs _ i).1) hx0S hi (fun n => hys _ i) (tendsto_pi_nhds.1 l3 i)
  have hsum : Filter.Tendsto (fun n => ∑ i, (w (φ n) i) • ys (φ n) i) Filter.atTop
      (nhds (∑ i, (w0 i) • ys0 i)) :=
    tendsto_finsetSum _ fun i _ =>
      (tendsto_pi_nhds.1 l4 i).smul (tendsto_pi_nhds.1 l3 i)
  have hx0eq : x0 = ∑ i, (w0 i) • ys0 i :=
    tendsto_nhds_unique l1 (by simpa only [← hx2 (φ _)] using hsum)
  refine ⟨x0, hx0S, ?_⟩
  have hmemΦ : ∑ i, (w0 i) • ys0 i ∈ Φ x0 :=
    (hΦ x0 hx0S).2.2.sum_mem (fun i _ => hw0.1 i) hw0.2 (fun i _ => hys0 i)
  rwa [← hx0eq] at hmemΦ

-- Prove2me | solution 2 for Kakutani1941.FixedPoint.kakutani_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T03:03:08.253787+00:00
-- url     : https://prove2.me/submissions/a5aedcec-225f-4830-a874-0439f4afdb98

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
import Theorems.Thm_AGT_brouwer_fixed_point

-- carved verbatim out of submission ed077460-16ce-4cc1-8af8-efd98b2a9a91, lines 1218-1234

section
set_option autoImplicit false
open Kakutani1941
open Kakutani1941.FixedPoint
open Set Metric Finset

lemma exists_approximate_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Set E) (hSc : IsCompact S) (hSv : Convex ℝ S)
    (hSn : S.Nonempty) (Φ : E → Set E) (hsub : ∀ x ∈ S, Φ x ⊆ S)
    (hne : ∀ x ∈ S, (Φ x).Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, ∀ (L : E →L[ℝ] ℝ) (c : ℝ),
      (∀ u ∈ S, dist u x < ε → ∀ v ∈ Φ u, L v ≤ c) → L x ≤ c := by
  classical
  obtain ⟨t,htS,htfin,htcover⟩ := hSc.finite_cover_balls hε
  let F : Finset E := htfin.toFinset
  have hFS : ∀ a ∈ F, a ∈ S := fun a ha => htS (htfin.mem_toFinset.mp ha)
  let ψ : E → E := fun a => if ha : a ∈ S then (hne a ha).choose else hSn.choose
  have hψ : ∀ a ∈ F, ψ a ∈ Φ a := by
    intro a ha
    dsimp [ψ]
    rw [dif_pos (hFS a ha)]
    exact (hne a (hFS a ha)).choose_spec
  let q : E → E → ℝ := fun a x => max (ε-dist x a) 0
  let D : E → ℝ := fun x => ∑ a ∈ F, q a x
  have hq : ∀ a x, 0 ≤ q a x := fun a x => le_max_right _ _
  have hD : ∀ x ∈ S, 0 < D x := by
    intro x hx
    obtain ⟨a,hat,hxa⟩ := Set.mem_iUnion₂.mp (htcover hx)
    have ha : a ∈ F := htfin.mem_toFinset.mpr hat
    have hpos : 0 < q a x := lt_max_of_lt_left (sub_pos.mpr hxa)
    exact hpos.trans_le (Finset.single_le_sum (fun b _ => hq b x) ha)
  let w : E → E → ℝ := fun a x => q a x / D x
  have hw : ∀ x ∈ S, ∀ a, 0 ≤ w a x := fun x hx a => div_nonneg (hq a x) (hD x hx).le
  have hsum : ∀ x ∈ S, ∑ a ∈ F, w a x = 1 := by
    intro x hx
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self (hD x hx).ne'
  let f : E → E := fun x => ∑ a ∈ F, w a x • ψ a
  have hqc : ∀ a, Continuous (q a) := by intro a; dsimp [q]; fun_prop
  have hDc : Continuous D := by dsimp [D]; fun_prop
  have hfc : ContinuousOn f S := by
    apply continuousOn_finsetSum
    intro a _
    exact ((hqc a).continuousOn.div hDc.continuousOn (fun x hx => (hD x hx).ne')).smul continuousOn_const
  have hfm : Set.MapsTo f S S := by
    intro x hx
    exact hSv.sum_mem (fun a _ => hw x hx a) (hsum x hx)
      (fun a ha => hsub a (hFS a ha) (hψ a ha))
  obtain ⟨x,hx,hfix⟩ := AGT.brouwer_fixed_point hSv hSc hSn f hfc hfm
  refine ⟨x,hx,?_⟩
  intro L c hlocal
  have hterm : ∀ a ∈ F, w a x * L (ψ a) ≤ w a x * c := by
    intro a ha
    by_cases hz : w a x = 0
    · simp [hz]
    · have hqne : q a x ≠ 0 := by
        intro hzero
        apply hz
        simp [w,hzero]
      have hdist : dist a x < ε := by
        by_contra hn
        have hle : ε-dist x a ≤ 0 := by rw [dist_comm x a]; linarith
        exact hqne (max_eq_right hle)
      exact mul_le_mul_of_nonneg_left (hlocal a (hFS a ha) hdist (ψ a) (hψ a ha)) (hw x hx a)
  have he : L x = ∑ a ∈ F, w a x * L (ψ a) := by
    conv_lhs => rw [← hfix]
    simp only [f,map_sum,map_smul,smul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ a ∈ F, w a x * c := Finset.sum_le_sum hterm
    _ = c := by rw [← Finset.sum_mul,hsum x hx,one_mul]

end

section
set_option autoImplicit false
open Set Filter Topology Metric
open Kakutani1941
open Kakutani1941.FixedPoint
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma graph_closed {S : Set E} (hS : IsClosed S) (Φ : E → Set E)
    (husc : IsUpperSemicontinuous S Φ) :
    IsClosed {p : E × E | p.1 ∈ S ∧ p.2 ∈ Φ p.1} := by
  apply IsSeqClosed.isClosed
  intro u p hu hup
  have hx : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hup
  have hy : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hup
  have hpS : p.1 ∈ S := hS.mem_of_tendsto hx (Eventually.of_forall (fun n => (hu n).1))
  exact ⟨hpS, husc (fun n => (u n).1) (fun n => (u n).2) p.1 p.2
    (fun n => (hu n).1) hpS hx (fun n => (hu n).2) hy⟩

lemma local_upper_bound {S : Set E} (hS : IsCompact S) (Φ : E → Set E)
    (hsub : ∀ x ∈ S, Φ x ⊆ S) (husc : IsUpperSemicontinuous S Φ)
    (g : E → ℝ) (hg : Continuous g) (x : E) (c : ℝ)
    (hxc : ∀ y ∈ Φ x, g y < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, dist s x < δ → ∀ y ∈ Φ s, g y < c := by
  let bad : Set (E × E) := {p | p.1 ∈ S ∧ p.2 ∈ Φ p.1} ∩ {p | c ≤ g p.2}
  have hbadclosed : IsClosed bad :=
    (graph_closed hS.isClosed Φ husc).inter
      (isClosed_le continuous_const (hg.comp continuous_snd))
  have hbadcompact : IsCompact bad := (hS.prod hS).of_isClosed_subset hbadclosed
    (fun p hp => ⟨hp.1.1, hsub p.1 hp.1.1 hp.1.2⟩)
  have himage : IsClosed (Prod.fst '' bad) := (hbadcompact.image continuous_fst).isClosed
  have hx : x ∈ (Prod.fst '' bad)ᶜ := by
    rintro ⟨p, hp, hpfirst⟩
    have hmem : p.2 ∈ Φ x := hpfirst ▸ hp.1.2
    exact (not_le_of_gt (hxc p.2 hmem)) hp.2
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp himage.isOpen_compl x hx
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsx y hy
  by_contra h
  have hp : (s, y) ∈ bad := ⟨⟨hs, hy⟩, le_of_not_gt h⟩
  exact (hball (mem_ball.mpr hsx)) ⟨(s, y), hp, rfl⟩

lemma fixed_point_of_approximations (S : Set E) (hS : IsCompact S) (Φ : E → Set E)
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (husc : IsUpperSemicontinuous S Φ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x ∈ S, ∀ (L : E →L[ℝ] ℝ) (c : ℝ),
      (∀ u ∈ S, dist u x < ε → ∀ v ∈ Φ u, L v ≤ c) → L x ≤ c) :
    ∃ x ∈ S, x ∈ Φ x := by
  choose x hx hprop using fun n : ℕ =>
    happrox (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨x₀, hx₀, φ, hφ, hlim⟩ := hS.tendsto_subseq hx
  refine ⟨x₀, hx₀, ?_⟩
  by_contra hnot
  obtain ⟨L, c, hsep, hcx⟩ := geometric_hahn_banach_closed_point
    (hΦ x₀ hx₀).2.2 (hΦ x₀ hx₀).2.1 hnot
  obtain ⟨δ, hδ, hlocal⟩ := local_upper_bound hS Φ (fun s hs => (hΦ s hs).1)
    husc L L.continuous x₀ c hsep
  have hnear : ∀ᶠ n in atTop, dist (x (φ n)) x₀ < δ / 2 := by
    exact hlim.eventually (ball_mem_nhds x₀ (half_pos hδ))
  have hepslim : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have heps : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < δ / 2 :=
    hepslim.eventually (gt_mem_nhds (half_pos hδ))
  have hle : ∀ᶠ n in atTop, L (x (φ n)) ≤ c := by
    filter_upwards [hnear, heps] with n hnx hnε
    apply hprop (φ n) L c
    intro u hu hun v hv
    have hux : dist u x₀ < δ := by
      have ht := dist_triangle u (x (φ n)) x₀
      linarith
    exact (hlocal u hu hux v hv).le
  have hfinal : L x₀ ≤ c := le_of_tendsto (L.continuous.continuousAt.tendsto.comp hlim) hle
  exact (not_le_of_gt hcx) hfinal

end

section
set_option autoImplicit false
open Kakutani1941
open Kakutani1941.FixedPoint

theorem kakutani_fixed_point {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by
  have hSc : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hSclosed,hSbounded⟩
  exact fixed_point_of_approximations S hSc Φ hΦ husc
    (fun ε hε => exists_approximate_fixed_point S hSc hSconvex hSnonempty Φ
      (fun x hx => (hΦ x hx).1) hΦne ε hε)

end

section
set_option autoImplicit false
open Kakutani1941.FixedPoint

theorem solution {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by
  exact kakutani_fixed_point hSbounded hSclosed hSconvex hSnonempty Φ hΦ hΦne husc

end

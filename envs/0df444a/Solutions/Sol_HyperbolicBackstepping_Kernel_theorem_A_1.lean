-- Prove2me | solution 1 for HyperbolicBackstepping.Kernel.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T12:02:56.821792+00:00
-- url     : https://prove2.me/submissions/9ce17656-1da2-4467-b978-c9fd56d644f8

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

set_option autoImplicit false
set_option linter.unusedSectionVars false

open HyperbolicBackstepping.Kernel Set Filter Topology

namespace HBK

/-! ### Generic travel-time primitives -/

noncomputable def P (e : ℝ → ℝ) (x : ℝ) : ℝ := ∫ z in (0:ℝ)..x, 1 / e z

noncomputable def clamp (x : ℝ) : ℝ := max 0 (min x 1)

lemma clamp_mem (x : ℝ) : clamp x ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clamp_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : clamp x = x := by
  unfold clamp; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma continuous_clamp : Continuous clamp := by unfold clamp; fun_prop

lemma clamp_mono {x y : ℝ} (h : x ≤ y) : clamp x ≤ clamp y := by
  unfold clamp; exact max_le_max le_rfl (min_le_min_right _ h)

lemma clamp_lip {x y : ℝ} (h : x ≤ y) : clamp y - clamp x ≤ y - x := by
  simp only [clamp, max_def, min_def]; split_ifs <;> linarith

lemma clamp_of_le {x : ℝ} (h : x ≤ 0) : clamp x = 0 := by
  unfold clamp; rw [min_eq_left (by linarith), max_eq_left h]

lemma clamp_of_ge {x : ℝ} (h : 1 ≤ x) : clamp x = 1 := by
  unfold clamp; rw [min_eq_right h, max_eq_right zero_le_one]

noncomputable def Pe (e : ℝ → ℝ) (x : ℝ) : ℝ := P e (clamp x) + (x - clamp x)

section generic
variable {e : ℝ → ℝ} (hc : ContinuousOn e (Icc 0 1)) (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < e x)
include hc hp

lemma inv_contOn : ContinuousOn (fun z => 1 / e z) (Icc 0 1) :=
  continuousOn_const.div hc (fun x hx => (hp x hx).ne')

lemma P_contOn : ContinuousOn (P e) (Icc 0 1) := by
  have hI : MeasureTheory.IntegrableOn (fun z => 1 / e z) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]; exact (inv_contOn hc hp).integrableOn_Icc
  have h := intervalIntegral.continuousOn_primitive_interval hI
  rw [uIcc_of_le zero_le_one] at h
  exact h

lemma P_sub {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    P e b - P e a = ∫ z in a..b, 1 / e z := by
  unfold P
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hint : ∀ u v : ℝ, u ∈ Icc (0:ℝ) 1 → v ∈ Icc (0:ℝ) 1 →
      IntervalIntegrable (fun z => 1 / e z) MeasureTheory.volume u v := fun u v hu hv =>
    ((inv_contOn hc hp).mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  exact intervalIntegral.integral_interval_sub_left (hint 0 b h0 hb) (hint 0 a h0 ha)

lemma P_strict : StrictMonoOn (P e) (Icc 0 1) := by
  intro a ha b hb hab
  have h1 := P_sub hc hp ha hb
  have hpos : 0 < ∫ z in a..b, 1 / e z :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (((inv_contOn hc hp).mono (uIcc_subset_Icc ha hb)).intervalIntegrable)
      (fun z hz => one_div_pos.mpr (hp z ⟨by linarith [hz.1, ha.1], by linarith [hz.2, hb.2]⟩)) hab
  linarith

lemma Pe_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : Pe e x = P e x := by
  simp [Pe, clamp_eq hx]

lemma Pe_cont : Continuous (Pe e) := by
  have h1 : Continuous (fun x => P e (clamp x)) :=
    (P_contOn hc hp).comp_continuous continuous_clamp clamp_mem
  unfold Pe
  exact h1.add (continuous_id.sub continuous_clamp)

lemma Pe_strictMono : StrictMono (Pe e) := by
  intro x y hxy
  unfold Pe
  have h1 := clamp_mono hxy.le
  have h2 := clamp_lip hxy.le
  rcases h1.lt_or_eq with h | h
  · have := P_strict hc hp (clamp_mem x) (clamp_mem y) h
    linarith
  · rw [h]; linarith

lemma Pe_atTop : Tendsto (Pe e) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (P e 1 - 1) tendsto_id)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  simp [Pe, clamp_of_ge hx]; linarith

lemma Pe_atBot : Tendsto (Pe e) atBot atBot := by
  refine tendsto_atBot_mono' atBot ?_ tendsto_id
  filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
  simp [Pe, clamp_of_le hx, P]

end generic

lemma Pe_zero (e : ℝ → ℝ) : Pe e 0 = 0 := by
  simp [Pe, clamp_eq (left_mem_Icc.2 (zero_le_one' ℝ)), P]

lemma Pe_of_ge (e : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x) : Pe e x = P e 1 + (x - 1) := by
  simp [Pe, clamp_of_ge hx]

lemma Pe_of_le (e : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) : Pe e x = x := by
  simp [Pe, clamp_of_le hx, P]

lemma Pe_sum_atTop (e e' : ℝ → ℝ) : Tendsto (fun x => Pe e x + Pe e' x) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_atTop_add_const_right atTop (P e 1 + P e' 1 - 2) tendsto_id)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [Pe_of_ge e hx, Pe_of_ge e' hx]; simp; linarith

lemma Pe_sum_atBot (e e' : ℝ → ℝ) : Tendsto (fun x => Pe e x + Pe e' x) atBot atBot := by
  refine tendsto_atBot_mono' atBot ?_ tendsto_id
  filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
  rw [Pe_of_le e hx, Pe_of_le e' hx]; simp; linarith

/-- generic inverse identification -/
lemma inv_spec (E : ℝ ≃o ℝ) {g : ℝ → ℝ} (hfg : ∀ x ∈ Icc (0:ℝ) 1, E x = g x) {y : ℝ}
    (hy : y ∈ Icc (E 0) (E 1)) : Function.invFunOn g (Icc 0 1) y = E.symm y := by
  set x := E.symm y with hxdef
  have hfx : E x = y := E.apply_symm_apply y
  have hx : x ∈ Icc (0:ℝ) 1 := ⟨E.le_symm_apply.2 hy.1, E.symm_apply_le.2 hy.2⟩
  have hgx : g x = y := by rw [← hfg x hx, hfx]
  obtain ⟨hm, he⟩ := Function.invFunOn_pos (f := g) (s := Icc (0:ℝ) 1) ⟨x, hx, hgx⟩
  apply E.injective
  rw [hfg _ hm, he, hfx]

/-! ### The order isomorphisms attached to `D` -/

section D
variable (D : GoursatData)

noncomputable def E1 : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (Pe D.eps1) (Pe_strictMono D.eps1_cont D.eps1_pos)
    ((Pe_cont D.eps1_cont D.eps1_pos).surjective (Pe_atTop D.eps1_cont D.eps1_pos)
      (Pe_atBot D.eps1_cont D.eps1_pos))

noncomputable def E2 : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (Pe D.eps2) (Pe_strictMono D.eps2_cont D.eps2_pos)
    ((Pe_cont D.eps2_cont D.eps2_pos).surjective (Pe_atTop D.eps2_cont D.eps2_pos)
      (Pe_atBot D.eps2_cont D.eps2_pos))

noncomputable def E3 : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun x => Pe D.eps1 x + Pe D.eps2 x)
    ((Pe_strictMono D.eps1_cont D.eps1_pos).add (Pe_strictMono D.eps2_cont D.eps2_pos))
    (((Pe_cont D.eps1_cont D.eps1_pos).add (Pe_cont D.eps2_cont D.eps2_pos)).surjective
      (Pe_sum_atTop D.eps1 D.eps2) (Pe_sum_atBot D.eps1 D.eps2))

lemma E3_eq (x : ℝ) : E3 D x = E1 D x + E2 D x := rfl

lemma E1_zero : E1 D 0 = 0 := Pe_zero _
lemma E2_zero : E2 D 0 = 0 := Pe_zero _
lemma E3_zero : E3 D 0 = 0 := by rw [E3_eq, E1_zero, E2_zero]; simp

lemma phi1_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : phi1 D x = E1 D x :=
  (Pe_eq D.eps1_cont D.eps1_pos hx).symm
lemma phi2_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : phi2 D x = E2 D x :=
  (Pe_eq D.eps2_cont D.eps2_pos hx).symm
lemma phi3_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : phi3 D x = E3 D x := by
  rw [E3_eq, phi3, phi1_eq D hx, phi2_eq D hx]

attribute [irreducible] E1 E2 E3

lemma inv1 {y : ℝ} (hy : y ∈ Icc 0 (E1 D 1)) : phiInv (phi1 D) y = (E1 D).symm y := by
  unfold phiInv
  exact inv_spec (E1 D) (fun x hx => (phi1_eq D hx).symm) (by rwa [E1_zero])
lemma inv2 {y : ℝ} (hy : y ∈ Icc 0 (E2 D 1)) : phiInv (phi2 D) y = (E2 D).symm y := by
  unfold phiInv
  exact inv_spec (E2 D) (fun x hx => (phi2_eq D hx).symm) (by rwa [E2_zero])
lemma inv3 {y : ℝ} (hy : y ∈ Icc 0 (E3 D 1)) : phiInv (phi3 D) y = (E3 D).symm y := by
  unfold phiInv
  exact inv_spec (E3 D) (fun x hx => (phi3_eq D hx).symm) (by rwa [E3_zero])

@[fun_prop] lemma E1_cont : Continuous (E1 D) := (E1 D).continuous
@[fun_prop] lemma E2_cont : Continuous (E2 D) := (E2 D).continuous
@[fun_prop] lemma E3_cont : Continuous (E3 D) := (E3 D).continuous
@[fun_prop] lemma E1s_cont : Continuous (E1 D).symm := (E1 D).symm.continuous
@[fun_prop] lemma E2s_cont : Continuous (E2 D).symm := (E2 D).symm.continuous
@[fun_prop] lemma E3s_cont : Continuous (E3 D).symm := (E3 D).symm.continuous

end D

end HBK

namespace HBK

/-! ### Global characteristic maps -/

section D2
variable (D : GoursatData)

noncomputable def st2 (x ξ : ℝ) : ℝ := (E3 D).symm (E1 D x + E2 D ξ)
noncomputable def st3 (x ξ : ℝ) : ℝ := (E3 D).symm (E2 D x + E1 D ξ)

noncomputable def sG (j : Fin 4) (x ξ : ℝ) : ℝ :=
  if j = 0 then E1 D ξ
  else if j = 1 then E1 D x - E1 D (st2 D x ξ)
  else if j = 2 then E2 D x - E2 D (st3 D x ξ)
  else E2 D ξ

noncomputable def cX (j : Fin 4) (x ξ s : ℝ) : ℝ :=
  if j = 0 then (E1 D).symm (E1 D x - E1 D ξ + s)
  else if j = 1 then (E1 D).symm (E1 D (st2 D x ξ) + s)
  else if j = 2 then (E2 D).symm (E2 D (st3 D x ξ) + s)
  else (E2 D).symm (E2 D x - E2 D ξ + s)

noncomputable def cXi (j : Fin 4) (x ξ s : ℝ) : ℝ :=
  if j = 0 then (E1 D).symm s
  else if j = 1 then (E2 D).symm (E2 D (st2 D x ξ) - s)
  else if j = 2 then (E1 D).symm (E1 D (st3 D x ξ) - s)
  else (E2 D).symm s

lemma sG_cont (j : Fin 4) : Continuous (fun p : ℝ × ℝ => sG D j p.1 p.2) := by
  unfold sG st2 st3; split_ifs <;> fun_prop

lemma cX_cont (j : Fin 4) : Continuous (fun q : (ℝ × ℝ) × ℝ => cX D j q.1.1 q.1.2 q.2) := by
  unfold cX st2 st3; split_ifs <;> fun_prop

lemma cXi_cont (j : Fin 4) : Continuous (fun q : (ℝ × ℝ) × ℝ => cXi D j q.1.1 q.1.2 q.2) := by
  unfold cXi st2 st3; split_ifs <;> fun_prop

lemma E1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ E1 D x := by
  rw [← E1_zero D]; exact (E1 D).monotone hx
lemma E2_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ E2 D x := by
  rw [← E2_zero D]; exact (E2 D).monotone hx

lemma mem_Tri {x ξ : ℝ} : (x, ξ) ∈ Tri ↔ 0 ≤ ξ ∧ ξ ≤ x ∧ x ≤ 1 := Iff.rfl

/-- the full package of facts for one characteristic -/
def Pack (j : Fin 4) (x ξ : ℝ) : Prop :=
  sF D j x ξ = sG D j x ξ ∧ 0 ≤ sG D j x ξ ∧ ∀ s ∈ Icc 0 (sG D j x ξ),
    charX D j x ξ s = cX D j x ξ s ∧ charXi D j x ξ s = cXi D j x ξ s ∧
    (cX D j x ξ s, cXi D j x ξ s) ∈ Tri ∧
    E3 D (cX D j x ξ s) ≤ E3 D x - (sG D j x ξ - s) ∧ cX D j x ξ s ≤ x

lemma start2_eq {x ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ x) (h2 : x ≤ 1) :
    start2 D x ξ = st2 D x ξ ∧ ξ ≤ st2 D x ξ ∧ st2 D x ξ ≤ x ∧
      E1 D (st2 D x ξ) + E2 D (st2 D x ξ) = E1 D x + E2 D ξ := by
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨h0.trans h1, h2⟩
  have hξI : ξ ∈ Icc (0:ℝ) 1 := ⟨h0, h1.trans h2⟩
  have a1 := E1_nonneg D (h0.trans h1)
  have a2 := E2_nonneg D h0
  have a3 : E1 D x ≤ E1 D 1 := (E1 D).monotone h2
  have a4 : E2 D ξ ≤ E2 D 1 := (E2 D).monotone (h1.trans h2)
  have a5 : E1 D ξ ≤ E1 D x := (E1 D).monotone h1
  have a6 : E2 D ξ ≤ E2 D x := (E2 D).monotone h1
  have e : E3 D (st2 D x ξ) = E1 D x + E2 D ξ := (E3 D).apply_symm_apply _
  rw [E3_eq] at e
  refine ⟨?_, ?_, ?_, e⟩
  · unfold start2 st2
    rw [phi1_eq D hxI, phi2_eq D hξI, inv3 D ⟨by linarith, by rw [E3_eq]; linarith⟩]
  · exact (E3 D).le_symm_apply.2 (by rw [E3_eq]; linarith)
  · exact (E3 D).symm_apply_le.2 (by rw [E3_eq]; linarith)

lemma start3_eq {x ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ x) (h2 : x ≤ 1) :
    start3 D x ξ = st3 D x ξ ∧ ξ ≤ st3 D x ξ ∧ st3 D x ξ ≤ x ∧
      E1 D (st3 D x ξ) + E2 D (st3 D x ξ) = E2 D x + E1 D ξ := by
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨h0.trans h1, h2⟩
  have hξI : ξ ∈ Icc (0:ℝ) 1 := ⟨h0, h1.trans h2⟩
  have a1 := E2_nonneg D (h0.trans h1)
  have a2 := E1_nonneg D h0
  have a3 : E2 D x ≤ E2 D 1 := (E2 D).monotone h2
  have a4 : E1 D ξ ≤ E1 D 1 := (E1 D).monotone (h1.trans h2)
  have a5 : E1 D ξ ≤ E1 D x := (E1 D).monotone h1
  have a6 : E2 D ξ ≤ E2 D x := (E2 D).monotone h1
  have e : E3 D (st3 D x ξ) = E2 D x + E1 D ξ := (E3 D).apply_symm_apply _
  rw [E3_eq] at e
  refine ⟨?_, ?_, ?_, e⟩
  · unfold start3 st3
    rw [phi2_eq D hxI, phi1_eq D hξI, inv3 D ⟨by linarith, by rw [E3_eq]; linarith⟩]
  · exact (E3 D).le_symm_apply.2 (by rw [E3_eq]; linarith)
  · exact (E3 D).symm_apply_le.2 (by rw [E3_eq]; linarith)

lemma pack0 {x ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ x) (h2 : x ≤ 1) : Pack D 0 x ξ := by
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨h0.trans h1, h2⟩
  have hξI : ξ ∈ Icc (0:ℝ) 1 := ⟨h0, h1.trans h2⟩
  have m1 : E1 D ξ ≤ E1 D x := (E1 D).monotone h1
  have m2 : E1 D x ≤ E1 D 1 := (E1 D).monotone h2
  have m3 := E1_nonneg D h0
  have hsG : sG D 0 x ξ = E1 D ξ := by simp [sG]
  refine ⟨by rw [hsG]; simp only [sF, if_pos rfl]; exact phi1_eq D hξI, by rw [hsG]; exact m3, ?_⟩
  intro s hs
  rw [hsG] at hs ⊢
  obtain ⟨hs0, hs1⟩ := hs
  have hcX : cX D 0 x ξ s = (E1 D).symm (E1 D x - E1 D ξ + s) := by simp [cX]
  have hcXi : cXi D 0 x ξ s = (E1 D).symm s := by simp [cXi]
  rw [hcX, hcXi]
  have ha : E1 D ((E1 D).symm (E1 D x - E1 D ξ + s)) = E1 D x - E1 D ξ + s :=
    (E1 D).apply_symm_apply _
  have hb : E1 D ((E1 D).symm s) = s := (E1 D).apply_symm_apply _
  have hax : (E1 D).symm (E1 D x - E1 D ξ + s) ≤ x := (E1 D).le_iff_le.1 (by rw [ha]; linarith)
  have hba : (E1 D).symm s ≤ (E1 D).symm (E1 D x - E1 D ξ + s) :=
    (E1 D).le_iff_le.1 (by rw [ha, hb]; linarith)
  have hb0 : 0 ≤ (E1 D).symm s := (E1 D).le_iff_le.1 (by rw [hb, E1_zero]; linarith)
  have e2 := (E2 D).monotone hax
  refine ⟨?_, ?_, ⟨hb0, hba, hax.trans h2⟩, ?_, hax⟩
  · simp [charX]
    rw [phi1_eq D hxI, phi1_eq D hξI, inv1 D ⟨by linarith, by linarith⟩]
  · simp [charXi]; rw [inv1 D ⟨hs0, by linarith⟩]
  · rw [E3_eq, E3_eq, ha]; linarith

lemma pack3 {x ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ x) (h2 : x ≤ 1) : Pack D 3 x ξ := by
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨h0.trans h1, h2⟩
  have hξI : ξ ∈ Icc (0:ℝ) 1 := ⟨h0, h1.trans h2⟩
  have m1 : E2 D ξ ≤ E2 D x := (E2 D).monotone h1
  have m2 : E2 D x ≤ E2 D 1 := (E2 D).monotone h2
  have m3 := E2_nonneg D h0
  have hsG : sG D 3 x ξ = E2 D ξ := by simp [sG]
  refine ⟨by rw [hsG]; simp [sF]; exact phi2_eq D hξI, by rw [hsG]; exact m3, ?_⟩
  intro s hs
  rw [hsG] at hs ⊢
  obtain ⟨hs0, hs1⟩ := hs
  have hcX : cX D 3 x ξ s = (E2 D).symm (E2 D x - E2 D ξ + s) := by simp [cX]
  have hcXi : cXi D 3 x ξ s = (E2 D).symm s := by simp [cXi]
  rw [hcX, hcXi]
  have ha : E2 D ((E2 D).symm (E2 D x - E2 D ξ + s)) = E2 D x - E2 D ξ + s :=
    (E2 D).apply_symm_apply _
  have hb : E2 D ((E2 D).symm s) = s := (E2 D).apply_symm_apply _
  have hax : (E2 D).symm (E2 D x - E2 D ξ + s) ≤ x := (E2 D).le_iff_le.1 (by rw [ha]; linarith)
  have hba : (E2 D).symm s ≤ (E2 D).symm (E2 D x - E2 D ξ + s) :=
    (E2 D).le_iff_le.1 (by rw [ha, hb]; linarith)
  have hb0 : 0 ≤ (E2 D).symm s := (E2 D).le_iff_le.1 (by rw [hb, E2_zero]; linarith)
  have e1 := (E1 D).monotone hax
  refine ⟨?_, ?_, ⟨hb0, hba, hax.trans h2⟩, ?_, hax⟩
  · simp [charX]
    rw [phi2_eq D hxI, phi2_eq D hξI, inv2 D ⟨by linarith, by linarith⟩]
  · simp [charXi]; rw [inv2 D ⟨hs0, by linarith⟩]
  · rw [E3_eq, E3_eq, ha]; linarith

lemma pack1 {x ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ x) (h2 : x ≤ 1) : Pack D 1 x ξ := by
  obtain ⟨hst, hξs, hsx, he⟩ := start2_eq D h0 h1 h2
  set st := st2 D x ξ with hst_def
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨h0.trans h1, h2⟩
  have hsI : st ∈ Icc (0:ℝ) 1 := ⟨h0.trans hξs, hsx.trans h2⟩
  have m1 : E1 D st ≤ E1 D x := (E1 D).monotone hsx
  have m2 : E1 D x ≤ E1 D 1 := (E1 D).monotone h2
  have m3 : E2 D ξ ≤ E2 D st := (E2 D).monotone hξs
  have m4 := E2_nonneg D h0
  have m5 : E2 D st ≤ E2 D 1 := (E2 D).monotone hsI.2
  have m6 := E1_nonneg D hsI.1
  have hsG : sG D 1 x ξ = E1 D x - E1 D st := by simp [sG, hst_def]
  refine ⟨?_, by rw [hsG]; linarith, ?_⟩
  · rw [hsG]; simp [sF]; rw [hst, phi1_eq D hxI, phi1_eq D hsI]
  intro s hs
  rw [hsG] at hs ⊢
  obtain ⟨hs0, hs1⟩ := hs
  have hcX : cX D 1 x ξ s = (E1 D).symm (E1 D st + s) := by simp [cX, hst_def]
  have hcXi : cXi D 1 x ξ s = (E2 D).symm (E2 D st - s) := by simp [cXi, hst_def]
  rw [hcX, hcXi]
  have ha : E1 D ((E1 D).symm (E1 D st + s)) = E1 D st + s := (E1 D).apply_symm_apply _
  have hb : E2 D ((E2 D).symm (E2 D st - s)) = E2 D st - s := (E2 D).apply_symm_apply _
  have hax : (E1 D).symm (E1 D st + s) ≤ x := (E1 D).le_iff_le.1 (by rw [ha]; linarith)
  have hsa : st ≤ (E1 D).symm (E1 D st + s) := (E1 D).le_iff_le.1 (by rw [ha]; linarith)
  have hbs : (E2 D).symm (E2 D st - s) ≤ st := (E2 D).le_iff_le.1 (by rw [hb]; linarith)
  have hξb : ξ ≤ (E2 D).symm (E2 D st - s) := (E2 D).le_iff_le.1 (by rw [hb]; linarith)
  have e2 := (E2 D).monotone hax
  refine ⟨?_, ?_, ⟨h0.trans hξb, hbs.trans hsa, hax.trans h2⟩, ?_, hax⟩
  · simp [charX]
    rw [hst, phi1_eq D hsI, inv1 D ⟨by linarith, by linarith⟩]
  · simp [charXi]
    rw [hst, phi2_eq D hsI, inv2 D ⟨by linarith, by linarith⟩]
  · rw [E3_eq, E3_eq, ha]; linarith

lemma pack2 {x ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ x) (h2 : x ≤ 1) : Pack D 2 x ξ := by
  obtain ⟨hst, hξs, hsx, he⟩ := start3_eq D h0 h1 h2
  set st := st3 D x ξ with hst_def
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨h0.trans h1, h2⟩
  have hsI : st ∈ Icc (0:ℝ) 1 := ⟨h0.trans hξs, hsx.trans h2⟩
  have m1 : E2 D st ≤ E2 D x := (E2 D).monotone hsx
  have m2 : E2 D x ≤ E2 D 1 := (E2 D).monotone h2
  have m3 : E1 D ξ ≤ E1 D st := (E1 D).monotone hξs
  have m4 := E1_nonneg D h0
  have m5 : E1 D st ≤ E1 D 1 := (E1 D).monotone hsI.2
  have m6 := E2_nonneg D hsI.1
  have hsG : sG D 2 x ξ = E2 D x - E2 D st := by simp [sG, hst_def]
  refine ⟨?_, by rw [hsG]; linarith, ?_⟩
  · rw [hsG]; simp [sF]; rw [hst, phi2_eq D hxI, phi2_eq D hsI]
  intro s hs
  rw [hsG] at hs ⊢
  obtain ⟨hs0, hs1⟩ := hs
  have hcX : cX D 2 x ξ s = (E2 D).symm (E2 D st + s) := by simp [cX, hst_def]
  have hcXi : cXi D 2 x ξ s = (E1 D).symm (E1 D st - s) := by simp [cXi, hst_def]
  rw [hcX, hcXi]
  have ha : E2 D ((E2 D).symm (E2 D st + s)) = E2 D st + s := (E2 D).apply_symm_apply _
  have hb : E1 D ((E1 D).symm (E1 D st - s)) = E1 D st - s := (E1 D).apply_symm_apply _
  have hax : (E2 D).symm (E2 D st + s) ≤ x := (E2 D).le_iff_le.1 (by rw [ha]; linarith)
  have hsa : st ≤ (E2 D).symm (E2 D st + s) := (E2 D).le_iff_le.1 (by rw [ha]; linarith)
  have hbs : (E1 D).symm (E1 D st - s) ≤ st := (E1 D).le_iff_le.1 (by rw [hb]; linarith)
  have hξb : ξ ≤ (E1 D).symm (E1 D st - s) := (E1 D).le_iff_le.1 (by rw [hb]; linarith)
  have e1 := (E1 D).monotone hax
  refine ⟨?_, ?_, ⟨h0.trans hξb, hbs.trans hsa, hax.trans h2⟩, ?_, hax⟩
  · simp [charX]
    rw [hst, phi2_eq D hsI, inv2 D ⟨by linarith, by linarith⟩]
  · simp [charXi]
    rw [hst, phi1_eq D hsI, inv1 D ⟨by linarith, by linarith⟩]
  · rw [E3_eq, E3_eq, ha]; linarith

lemma pack (j : Fin 4) {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) : Pack D j x ξ := by
  obtain ⟨h0, h1, h2⟩ := hx
  fin_cases j
  · exact pack0 D h0 h1 h2
  · exact pack1 D h0 h1 h2
  · exact pack2 D h0 h1 h2
  · exact pack3 D h0 h1 h2

end D2

end HBK

namespace HBK

/-! ### Retraction onto `Tri` and the global integral operator -/

noncomputable def rr (p : ℝ × ℝ) : ℝ × ℝ := (clamp p.1, max 0 (min p.2 (clamp p.1)))

lemma rr_mem (p : ℝ × ℝ) : rr p ∈ Tri := by
  have h := clamp_mem p.1
  exact ⟨le_max_left _ _, max_le h.1 (min_le_right _ _), h.2⟩

lemma rr_eq {p : ℝ × ℝ} (hp : p ∈ Tri) : rr p = p := by
  obtain ⟨h0, h1, h2⟩ := hp
  have hc : clamp p.1 = p.1 := clamp_eq ⟨h0.trans h1, h2⟩
  ext
  · simp [rr, hc]
  · simp [rr, hc, min_eq_left h1, max_eq_right h0]

lemma continuous_rr : Continuous rr := by
  have := continuous_clamp
  unfold rr; fun_prop

noncomputable def fr (f : ℝ → ℝ → ℝ) (y η : ℝ) : ℝ := f (rr (y, η)).1 (rr (y, η)).2

lemma fr_cont {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Tri) :
    Continuous (fun p : ℝ × ℝ => fr f p.1 p.2) := by
  have := hf.comp_continuous continuous_rr rr_mem
  exact this

lemma fr_eq (f : ℝ → ℝ → ℝ) {y η : ℝ} (h : (y, η) ∈ Tri) : fr f y η = f y η := by
  simp [fr, rr_eq h]

section D3
variable (D : GoursatData)

noncomputable def JG (j : Fin 4) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in (0:ℝ)..sG D j p.1 p.2, f (cX D j p.1 p.2 s) (cXi D j p.1 p.2 s)

lemma integrand_cont (j : Fin 4) {f : ℝ → ℝ → ℝ} (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    Continuous (fun q : (ℝ × ℝ) × ℝ => f (cX D j q.1.1 q.1.2 q.2) (cXi D j q.1.1 q.1.2 q.2)) :=
  hf.comp ((cX_cont D j).prodMk (cXi_cont D j))

lemma integrand_cont' (j : Fin 4) {f : ℝ → ℝ → ℝ} (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (p : ℝ × ℝ) : Continuous (fun s : ℝ => f (cX D j p.1 p.2 s) (cXi D j p.1 p.2 s)) :=
  (integrand_cont D j hf).comp (continuous_const.prodMk continuous_id)

lemma JG_cont (j : Fin 4) {f : ℝ → ℝ → ℝ} (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    Continuous (JG D j f) := by
  unfold JG
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := MeasureTheory.volume) (a₀ := (0:ℝ))
    (f := fun (p : ℝ × ℝ) (s : ℝ) => f (cX D j p.1 p.2 s) (cXi D j p.1 p.2 s))
    (integrand_cont D j hf) (sG_cont D j)
  exact h

lemma J_eq (j : Fin 4) (f : ℝ → ℝ → ℝ) {p : ℝ × ℝ} (hp : p ∈ Tri) :
    (∫ s in (0:ℝ)..sF D j p.1 p.2, f (charX D j p.1 p.2 s) (charXi D j p.1 p.2 s)) =
      JG D j (fr f) p := by
  obtain ⟨hsF, hpos, hP⟩ := pack D j (x := p.1) (ξ := p.2) hp
  unfold JG
  rw [hsF]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hpos] at hs
  obtain ⟨h1, h2, h3, -, -⟩ := hP s hs
  simp only [h1, h2, fr_eq f h3]

lemma Iop_eq (F : Fin 4 → ℝ → ℝ → ℝ) (j : Fin 4) {p : ℝ × ℝ} (hp : p ∈ Tri) :
    Iop D F j p.1 p.2 = ∑ i, JG D j (fr (fun y η => D.Cc j i y η * F i y η)) p := by
  unfold Iop
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact J_eq D j (fun y η => D.Cc j i y η * F i y η) hp

lemma Gint_eq (j : Fin 4) {p : ℝ × ℝ} (hp : p ∈ Tri) :
    Gint D j p.1 p.2 = JG D j (fr (D.g j)) p :=
  J_eq D j (D.g j) hp

lemma Gint_contOn (j : Fin 4) : ContinuousOn (fun p : ℝ × ℝ => Gint D j p.1 p.2) Tri :=
  (JG_cont D j (fr_cont (D.g_cont j))).continuousOn.congr (fun p hp => Gint_eq D j hp)

lemma Iop_contOn {F : Fin 4 → ℝ → ℝ → ℝ}
    (hF : ∀ i, ContinuousOn (fun p : ℝ × ℝ => F i p.1 p.2) Tri) (j : Fin 4) :
    ContinuousOn (fun p : ℝ × ℝ => Iop D F j p.1 p.2) Tri := by
  have hc : ∀ i, Continuous (JG D j (fr (fun y η => D.Cc j i y η * F i y η))) :=
    fun i => JG_cont D j (fr_cont ((D.Cc_cont j i).mul (hF i)))
  exact (continuous_finsetSum _ (fun i _ => hc i)).continuousOn.congr
    (fun p hp => Iop_eq D F j hp)

lemma x0_facts (j : Fin 4) {p : ℝ × ℝ} (hp : p ∈ Tri) :
    charX D j p.1 p.2 0 = cX D j p.1 p.2 0 ∧ charXi D j p.1 p.2 0 = cXi D j p.1 p.2 0 ∧
      (cX D j p.1 p.2 0, cXi D j p.1 p.2 0) ∈ Tri ∧ cX D j p.1 p.2 0 ≤ p.1 := by
  obtain ⟨-, hpos, hP⟩ := pack D j (x := p.1) (ξ := p.2) hp
  obtain ⟨h1, h2, h3, -, h5⟩ := hP 0 ⟨le_rfl, hpos⟩
  exact ⟨h1, h2, h3, h5⟩

lemma x0_cont (j : Fin 4) : Continuous (fun p : ℝ × ℝ => cX D j p.1 p.2 0) :=
  (cX_cont D j).comp (continuous_id.prodMk continuous_const)

lemma uX_contOn (j : Fin 4) {u : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ => u (charX D j p.1 p.2 0)) Tri := by
  have h : ContinuousOn (fun p : ℝ × ℝ => u (cX D j p.1 p.2 0)) Tri :=
    hu.comp (x0_cont D j).continuousOn (fun p hp => by
      obtain ⟨-, -, h3, -⟩ := x0_facts D j hp
      exact ⟨h3.1.trans h3.2.1, h3.2.2⟩)
  exact h.congr (fun p hp => by simp only [(x0_facts D j hp).1])

lemma comp_edge (j : Fin 4) {K : ℝ × ℝ → ℝ} (hK : ContinuousOn K Tri) :
    ContinuousOn (fun p : ℝ × ℝ => K (charX D j p.1 p.2 0, 0)) Tri := by
  have h : ContinuousOn (fun p : ℝ × ℝ => K (cX D j p.1 p.2 0, 0)) Tri :=
    hK.comp ((x0_cont D j).prodMk continuous_const).continuousOn (fun p hp => by
      obtain ⟨-, -, h3, -⟩ := x0_facts D j hp
      exact ⟨le_rfl, h3.1.trans h3.2.1, h3.2.2⟩)
  exact h.congr (fun p hp => by simp only [(x0_facts D j hp).1])

lemma H_contOn (j : Fin 4) : ContinuousOn (fun p : ℝ × ℝ => H D j p.1 p.2) Tri :=
  uX_contOn D j (D.h_cont j)

lemma src_contOn (j : Fin 4) : ContinuousOn (fun p : ℝ × ℝ => src D j p.1 p.2) Tri := by
  have hHG : ∀ k, ContinuousOn (fun p : ℝ × ℝ => H D k p.1 p.2 + Gint D k p.1 p.2) Tri :=
    fun k => (H_contOn D k).add (Gint_contOn D k)
  have hb : ContinuousOn (fun p : ℝ × ℝ => boundarySrc D j p.1 p.2) Tri := by
    by_cases h0 : j = 0
    · subst h0
      have e : ∀ p : ℝ × ℝ, boundarySrc D 0 p.1 p.2 =
          D.q 0 (charX D 0 p.1 p.2 0) *
              (H D 1 (charX D 0 p.1 p.2 0) 0 + Gint D 1 (charX D 0 p.1 p.2 0) 0) +
            D.q 1 (charX D 0 p.1 p.2 0) *
              (H D 2 (charX D 0 p.1 p.2 0) 0 + Gint D 2 (charX D 0 p.1 p.2 0) 0) :=
        fun p => if_pos rfl
      refine ContinuousOn.congr ?_ (fun p _ => e p)
      exact ((uX_contOn D 0 (D.q_cont 0)).mul (comp_edge D 0 (hHG 1))).add
        ((uX_contOn D 0 (D.q_cont 1)).mul (comp_edge D 0 (hHG 2)))
    by_cases h3 : j = 3
    · subst h3
      have e : ∀ p : ℝ × ℝ, boundarySrc D 3 p.1 p.2 =
          D.q 2 (charX D 3 p.1 p.2 0) *
              (H D 1 (charX D 3 p.1 p.2 0) 0 + Gint D 1 (charX D 3 p.1 p.2 0) 0) +
            D.q 3 (charX D 3 p.1 p.2 0) *
              (H D 2 (charX D 3 p.1 p.2 0) 0 + Gint D 2 (charX D 3 p.1 p.2 0) 0) :=
        fun p => (if_neg (by decide)).trans (if_pos rfl)
      refine ContinuousOn.congr ?_ (fun p _ => e p)
      exact ((uX_contOn D 3 (D.q_cont 2)).mul (comp_edge D 3 (hHG 1))).add
        ((uX_contOn D 3 (D.q_cont 3)).mul (comp_edge D 3 (hHG 2)))
    have e : ∀ p : ℝ × ℝ, boundarySrc D j p.1 p.2 = 0 :=
      fun p => (if_neg h0).trans (if_neg h3)
    exact continuousOn_const.congr (fun p _ => e p)
  exact ((H_contOn D j).add (Gint_contOn D j)).add hb

lemma PhiOp_contOn {F : Fin 4 → ℝ → ℝ → ℝ}
    (hF : ∀ i, ContinuousOn (fun p : ℝ × ℝ => F i p.1 p.2) Tri) (j : Fin 4) :
    ContinuousOn (fun p : ℝ × ℝ => PhiOp D F j p.1 p.2) Tri := by
  have hI : ∀ k, ContinuousOn (fun p : ℝ × ℝ => Iop D F k p.1 p.2) Tri := Iop_contOn D hF
  have hQ : ContinuousOn (fun p : ℝ × ℝ => Qop D F j p.1 p.2) Tri := by
    by_cases h0 : j = 0
    · subst h0
      have e : ∀ p : ℝ × ℝ, Qop D F 0 p.1 p.2 =
          D.q 0 (charX D 0 p.1 p.2 0) * Iop D F 1 (charX D 0 p.1 p.2 0) 0 +
            D.q 1 (charX D 0 p.1 p.2 0) * Iop D F 2 (charX D 0 p.1 p.2 0) 0 :=
        fun p => if_pos rfl
      refine ContinuousOn.congr ?_ (fun p _ => e p)
      exact ((uX_contOn D 0 (D.q_cont 0)).mul (comp_edge D 0 (hI 1))).add
        ((uX_contOn D 0 (D.q_cont 1)).mul (comp_edge D 0 (hI 2)))
    by_cases h3 : j = 3
    · subst h3
      have e : ∀ p : ℝ × ℝ, Qop D F 3 p.1 p.2 =
          D.q 2 (charX D 3 p.1 p.2 0) * Iop D F 1 (charX D 3 p.1 p.2 0) 0 +
            D.q 3 (charX D 3 p.1 p.2 0) * Iop D F 2 (charX D 3 p.1 p.2 0) 0 :=
        fun p => (if_neg (by decide)).trans (if_pos rfl)
      refine ContinuousOn.congr ?_ (fun p _ => e p)
      exact ((uX_contOn D 3 (D.q_cont 2)).mul (comp_edge D 3 (hI 1))).add
        ((uX_contOn D 3 (D.q_cont 3)).mul (comp_edge D 3 (hI 2)))
    have e : ∀ p : ℝ × ℝ, Qop D F j p.1 p.2 = 0 :=
      fun p => (if_neg h0).trans (if_neg h3)
    exact continuousOn_const.congr (fun p _ => e p)
  exact hQ.add (hI j)

/-! ### Estimates -/

lemma est (j : Fin 4) {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Tri)
    {L B : ℝ} (hL : 0 < L) (hB : 0 ≤ B)
    (hb : ∀ y η, (y, η) ∈ Tri → |f y η| ≤ B * Real.exp (L * E3 D y))
    {p : ℝ × ℝ} (hp : p ∈ Tri) :
    |JG D j (fr f) p| ≤ B * Real.exp (L * E3 D p.1) / L := by
  obtain ⟨-, hpos, hP⟩ := pack D j (x := p.1) (ξ := p.2) hp
  have hK0 : 0 ≤ B * Real.exp (L * E3 D p.1) := mul_nonneg hB (Real.exp_pos _).le
  have hbound : ∀ s ∈ Icc 0 (sG D j p.1 p.2),
      ‖fr f (cX D j p.1 p.2 s) (cXi D j p.1 p.2 s)‖ ≤
        B * Real.exp (L * E3 D p.1) * Real.exp (L * (s - sG D j p.1 p.2)) := by
    intro s hs
    obtain ⟨-, -, h3, h4, -⟩ := hP s hs
    rw [Real.norm_eq_abs, fr_eq f h3]
    refine (hb _ _ h3).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left h4 hL.le
    nlinarith
  have hint : ∫ s in (0:ℝ)..sG D j p.1 p.2,
      B * Real.exp (L * E3 D p.1) * Real.exp (L * (s - sG D j p.1 p.2)) =
      B * Real.exp (L * E3 D p.1) *
        ((1 - Real.exp (L * (0 - sG D j p.1 p.2))) / L) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hd : ∀ s ∈ uIcc (0:ℝ) (sG D j p.1 p.2),
        HasDerivAt (fun s => Real.exp (L * (s - sG D j p.1 p.2)) / L)
          (Real.exp (L * (s - sG D j p.1 p.2))) s := by
      intro s _
      have h1 : HasDerivAt (fun s => L * (s - sG D j p.1 p.2)) L s := by
        simpa using ((hasDerivAt_id s).sub_const (sG D j p.1 p.2)).const_mul L
      have h2 := (h1.exp).div_const L
      rw [mul_div_cancel_right₀ _ hL.ne'] at h2
      exact h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun s => Real.exp (L * (s - sG D j p.1 p.2))).intervalIntegrable
        _ _)]
    simp only [sub_self, mul_zero, Real.exp_zero]
    ring
  have hcont := integrand_cont' D j (fr_cont hf) p
  calc |JG D j (fr f) p|
      = ‖∫ s in (0:ℝ)..sG D j p.1 p.2, fr f (cX D j p.1 p.2 s) (cXi D j p.1 p.2 s)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∫ s in (0:ℝ)..sG D j p.1 p.2,
          B * Real.exp (L * E3 D p.1) * Real.exp (L * (s - sG D j p.1 p.2)) := by
        apply intervalIntegral.norm_integral_le_of_norm_le hpos
        · exact Filter.Eventually.of_forall (fun s hs => hbound s (Ioc_subset_Icc_self hs))
        · exact (by fun_prop : Continuous fun s =>
            B * Real.exp (L * E3 D p.1) * Real.exp (L * (s - sG D j p.1 p.2))).intervalIntegrable _ _
    _ = B * Real.exp (L * E3 D p.1) * ((1 - Real.exp (L * (0 - sG D j p.1 p.2))) / L) := hint
    _ ≤ B * Real.exp (L * E3 D p.1) / L := by
        have he := Real.exp_pos (L * (0 - sG D j p.1 p.2))
        have hLi := inv_pos.2 hL
        have := mul_nonneg (mul_nonneg hK0 hLi.le) he.le
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith

lemma JG_sub (j : Fin 4) {a b : ℝ → ℝ → ℝ} (ha : Continuous (fun p : ℝ × ℝ => a p.1 p.2))
    (hb : Continuous (fun p : ℝ × ℝ => b p.1 p.2)) (p : ℝ × ℝ) :
    JG D j a p - JG D j b p = JG D j (fun y η => a y η - b y η) p := by
  unfold JG
  exact (intervalIntegral.integral_sub ((integrand_cont' D j ha p).intervalIntegrable _ _)
    ((integrand_cont' D j hb p).intervalIntegrable _ _)).symm

lemma Iop_diff {F F' : Fin 4 → ℝ → ℝ → ℝ}
    (hF : ∀ i, ContinuousOn (fun p : ℝ × ℝ => F i p.1 p.2) Tri)
    (hF' : ∀ i, ContinuousOn (fun p : ℝ × ℝ => F' i p.1 p.2) Tri)
    {Cm M L : ℝ} (hL : 0 < L) (hCm0 : 0 ≤ Cm) (hM0 : 0 ≤ M)
    (hCm : ∀ j i y η, (y, η) ∈ Tri → |D.Cc j i y η| ≤ Cm)
    (hM : ∀ i y η, (y, η) ∈ Tri → |F i y η - F' i y η| ≤ M * Real.exp (L * E3 D y))
    (j : Fin 4) {p : ℝ × ℝ} (hp : p ∈ Tri) :
    |Iop D F j p.1 p.2 - Iop D F' j p.1 p.2| ≤ 4 * (Cm * M * Real.exp (L * E3 D p.1) / L) := by
  rw [Iop_eq D F j hp, Iop_eq D F' j hp, ← Finset.sum_sub_distrib]
  have hterm : ∀ i, |JG D j (fr (fun y η => D.Cc j i y η * F i y η)) p -
      JG D j (fr (fun y η => D.Cc j i y η * F' i y η)) p| ≤
        Cm * M * Real.exp (L * E3 D p.1) / L := by
    intro i
    have hc1 : ContinuousOn (fun q : ℝ × ℝ => D.Cc j i q.1 q.2 * F i q.1 q.2) Tri :=
      (D.Cc_cont j i).mul (hF i)
    have hc2 : ContinuousOn (fun q : ℝ × ℝ => D.Cc j i q.1 q.2 * F' i q.1 q.2) Tri :=
      (D.Cc_cont j i).mul (hF' i)
    rw [JG_sub D j (fr_cont hc1) (fr_cont hc2)]
    have hc3 : ContinuousOn
        (fun q : ℝ × ℝ => D.Cc j i q.1 q.2 * F i q.1 q.2 - D.Cc j i q.1 q.2 * F' i q.1 q.2) Tri :=
      hc1.sub hc2
    have hbd : ∀ y η, (y, η) ∈ Tri →
        |D.Cc j i y η * F i y η - D.Cc j i y η * F' i y η| ≤ Cm * M * Real.exp (L * E3 D y) := by
      intro y η h
      rw [← mul_sub, abs_mul, mul_assoc]
      exact mul_le_mul (hCm j i y η h) (hM i y η h) (abs_nonneg _) hCm0
    exact est D j hc3 hL (mul_nonneg hCm0 hM0) hbd hp
  calc |∑ i, (JG D j (fr (fun y η => D.Cc j i y η * F i y η)) p -
        JG D j (fr (fun y η => D.Cc j i y η * F' i y η)) p)|
      ≤ ∑ i, |JG D j (fr (fun y η => D.Cc j i y η * F i y η)) p -
        JG D j (fr (fun y η => D.Cc j i y η * F' i y η)) p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, Cm * M * Real.exp (L * E3 D p.1) / L := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 4 * (Cm * M * Real.exp (L * E3 D p.1) / L) := by simp

end D3

end HBK

namespace HBK

section D4
variable (D : GoursatData)

lemma src_def (j : Fin 4) (x ξ : ℝ) :
    src D j x ξ = H D j x ξ + Gint D j x ξ + boundarySrc D j x ξ := rfl
lemma PhiOp_def (F : Fin 4 → ℝ → ℝ → ℝ) (j : Fin 4) (x ξ : ℝ) :
    PhiOp D F j x ξ = Qop D F j x ξ + Iop D F j x ξ := rfl

lemma bsrc0 (x ξ : ℝ) : boundarySrc D 0 x ξ =
    D.q 0 (charX D 0 x ξ 0) * (H D 1 (charX D 0 x ξ 0) 0 + Gint D 1 (charX D 0 x ξ 0) 0) +
      D.q 1 (charX D 0 x ξ 0) * (H D 2 (charX D 0 x ξ 0) 0 + Gint D 2 (charX D 0 x ξ 0) 0) :=
  if_pos rfl
lemma bsrc3 (x ξ : ℝ) : boundarySrc D 3 x ξ =
    D.q 2 (charX D 3 x ξ 0) * (H D 1 (charX D 3 x ξ 0) 0 + Gint D 1 (charX D 3 x ξ 0) 0) +
      D.q 3 (charX D 3 x ξ 0) * (H D 2 (charX D 3 x ξ 0) 0 + Gint D 2 (charX D 3 x ξ 0) 0) :=
  (if_neg (by decide)).trans (if_pos rfl)
lemma bsrcZ {j : Fin 4} (h0 : j ≠ 0) (h3 : j ≠ 3) (x ξ : ℝ) : boundarySrc D j x ξ = 0 :=
  (if_neg h0).trans (if_neg h3)

lemma Qop0 (F : Fin 4 → ℝ → ℝ → ℝ) (x ξ : ℝ) : Qop D F 0 x ξ =
    D.q 0 (charX D 0 x ξ 0) * Iop D F 1 (charX D 0 x ξ 0) 0 +
      D.q 1 (charX D 0 x ξ 0) * Iop D F 2 (charX D 0 x ξ 0) 0 :=
  if_pos rfl
lemma Qop3 (F : Fin 4 → ℝ → ℝ → ℝ) (x ξ : ℝ) : Qop D F 3 x ξ =
    D.q 2 (charX D 3 x ξ 0) * Iop D F 1 (charX D 3 x ξ 0) 0 +
      D.q 3 (charX D 3 x ξ 0) * Iop D F 2 (charX D 3 x ξ 0) 0 :=
  (if_neg (by decide)).trans (if_pos rfl)
lemma QopZ (F : Fin 4 → ℝ → ℝ → ℝ) {j : Fin 4} (h0 : j ≠ 0) (h3 : j ≠ 3) (x ξ : ℝ) :
    Qop D F j x ξ = 0 :=
  (if_neg h0).trans (if_neg h3)

lemma Gint_zero {j : Fin 4} {x ξ : ℝ} (h : sF D j x ξ = 0) : Gint D j x ξ = 0 := by
  unfold Gint; rw [h]; simp

lemma Iop_zero (F : Fin 4 → ℝ → ℝ → ℝ) {j : Fin 4} {x ξ : ℝ} (h : sF D j x ξ = 0) :
    Iop D F j x ξ = 0 := by
  unfold Iop; simp [h]

lemma x0f (j : Fin 4) {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) :
    charX D j x ξ 0 = cX D j x ξ 0 ∧ charXi D j x ξ 0 = cXi D j x ξ 0 ∧
      (cX D j x ξ 0, cXi D j x ξ 0) ∈ Tri ∧ cX D j x ξ 0 ≤ x :=
  x0_facts D j (p := (x, ξ)) hx

lemma E1s_zero : (E1 D).symm 0 = 0 := (E1 D).symm_apply_eq.2 (E1_zero D).symm
lemma E2s_zero : (E2 D).symm 0 = 0 := (E2 D).symm_apply_eq.2 (E2_zero D).symm

/-- foot of characteristic 0 (or 3): on the edge `ξ = 0`, inside `[0,1]` -/
lemma foot0 {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) :
    charXi D 0 x ξ 0 = 0 ∧ charX D 0 x ξ 0 ∈ Icc (0:ℝ) 1 := by
  obtain ⟨h1, h2, h3, -⟩ := x0f D 0 hx
  obtain ⟨a, b, c⟩ := h3
  refine ⟨?_, ?_⟩
  · rw [h2]; simp [cXi, E1s_zero]
  · rw [h1]; exact ⟨a.trans b, c⟩

lemma foot3 {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) :
    charXi D 3 x ξ 0 = 0 ∧ charX D 3 x ξ 0 ∈ Icc (0:ℝ) 1 := by
  obtain ⟨h1, h2, h3, -⟩ := x0f D 3 hx
  obtain ⟨a, b, c⟩ := h3
  refine ⟨?_, ?_⟩
  · rw [h2]; simp [cXi, E2s_zero]
  · rw [h1]; exact ⟨a.trans b, c⟩

lemma diag1_pt {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) :
    charX D 1 x ξ 0 = start2 D x ξ ∧ charXi D 1 x ξ 0 = start2 D x ξ ∧
      start2 D x ξ ∈ Icc (0:ℝ) 1 := by
  obtain ⟨h1, h2, -⟩ := x0f D 1 hx
  obtain ⟨a, b, c⟩ := hx
  obtain ⟨hst, hξs, hsx, -⟩ := start2_eq D a b c
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hst]; simp [cX]
  · rw [h2, hst]; simp [cXi]
  · rw [hst]; exact ⟨a.trans hξs, hsx.trans c⟩

lemma diag2_pt {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) :
    charX D 2 x ξ 0 = start3 D x ξ ∧ charXi D 2 x ξ 0 = start3 D x ξ ∧
      start3 D x ξ ∈ Icc (0:ℝ) 1 := by
  obtain ⟨h1, h2, -⟩ := x0f D 2 hx
  obtain ⟨a, b, c⟩ := hx
  obtain ⟨hst, hξs, hsx, -⟩ := start3_eq D a b c
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hst]; simp [cX]
  · rw [h2, hst]; simp [cXi]
  · rw [hst]; exact ⟨a.trans hξs, hsx.trans c⟩

lemma edge0_at {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) : sF D 0 y 0 = 0 ∧ charX D 0 y 0 0 = y := by
  have hT : (y, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
  obtain ⟨hsF, -, -⟩ := pack D 0 hT
  obtain ⟨h1, -⟩ := x0f D 0 hT
  refine ⟨?_, ?_⟩
  · rw [hsF]; simp [sG, E1_zero]
  · rw [h1]; simp [cX, E1_zero]

lemma edge3_at {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) : sF D 3 y 0 = 0 ∧ charX D 3 y 0 0 = y := by
  have hT : (y, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
  obtain ⟨hsF, -, -⟩ := pack D 3 hT
  obtain ⟨h1, -⟩ := x0f D 3 hT
  refine ⟨?_, ?_⟩
  · rw [hsF]; simp [sG, E2_zero]
  · rw [h1]; simp [cX, E2_zero]

lemma diag1_at {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) : sF D 1 y y = 0 ∧ charX D 1 y y 0 = y := by
  have hT : (y, y) ∈ Tri := ⟨hy.1, le_rfl, hy.2⟩
  obtain ⟨hst, h1, h2, -⟩ := start2_eq D hy.1 le_rfl hy.2
  have hs : st2 D y y = y := le_antisymm h2 h1
  obtain ⟨hsF, -, -⟩ := pack D 1 hT
  obtain ⟨hX, -, -⟩ := diag1_pt D hT
  refine ⟨?_, ?_⟩
  · rw [hsF]; simp [sG, hs]
  · rw [hX, hst, hs]

lemma diag2_at {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) : sF D 2 y y = 0 ∧ charX D 2 y y 0 = y := by
  have hT : (y, y) ∈ Tri := ⟨hy.1, le_rfl, hy.2⟩
  obtain ⟨hst, h1, h2, -⟩ := start3_eq D hy.1 le_rfl hy.2
  have hs : st3 D y y = y := le_antisymm h2 h1
  obtain ⟨hsF, -, -⟩ := pack D 2 hT
  obtain ⟨hX, -, -⟩ := diag2_pt D hT
  refine ⟨?_, ?_⟩
  · rw [hsF]; simp [sG, hs]
  · rw [hX, hst, hs]

/-! ### Fixed-point form ⇒ characteristic solution -/

lemma fix_char {F : Fin 4 → ℝ → ℝ → ℝ}
    (hfix : ∀ j x ξ, (x, ξ) ∈ Tri → F j x ξ = src D j x ξ + PhiOp D F j x ξ) :
    IsCharSolution D F := by
  have s1 : ∀ x ξ, (x, ξ) ∈ Tri → F 1 x ξ = H D 1 x ξ + Gint D 1 x ξ + Iop D F 1 x ξ := by
    intro x ξ hx
    rw [hfix 1 x ξ hx, src_def, PhiOp_def, bsrcZ D (by decide) (by decide),
      QopZ D F (by decide) (by decide)]; ring
  have s2 : ∀ x ξ, (x, ξ) ∈ Tri → F 2 x ξ = H D 2 x ξ + Gint D 2 x ξ + Iop D F 2 x ξ := by
    intro x ξ hx
    rw [hfix 2 x ξ hx, src_def, PhiOp_def, bsrcZ D (by decide) (by decide),
      QopZ D F (by decide) (by decide)]; ring
  have dg1 : ∀ y ∈ Icc (0:ℝ) 1, F 1 y y = D.h 1 y := by
    intro y hy
    obtain ⟨hsF, hX⟩ := diag1_at D hy
    have hH : H D 1 y y = D.h 1 y := congrArg (D.h 1) hX
    rw [s1 y y ⟨hy.1, le_rfl, hy.2⟩, Gint_zero D hsF, Iop_zero D F hsF, hH]; ring
  have dg2 : ∀ y ∈ Icc (0:ℝ) 1, F 2 y y = D.h 2 y := by
    intro y hy
    obtain ⟨hsF, hX⟩ := diag2_at D hy
    have hH : H D 2 y y = D.h 2 y := congrArg (D.h 2) hX
    rw [s2 y y ⟨hy.1, le_rfl, hy.2⟩, Gint_zero D hsF, Iop_zero D F hsF, hH]; ring
  have ed1 : ∀ y ∈ Icc (0:ℝ) 1, F 0 y 0 = D.h 0 y + D.q 0 y * F 1 y 0 + D.q 1 y * F 2 y 0 := by
    intro y hy
    have hT : (y, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
    obtain ⟨hsF, hX⟩ := edge0_at D hy
    have hH : H D 0 y 0 = D.h 0 y := congrArg (D.h 0) hX
    rw [hfix 0 y 0 hT, s1 y 0 hT, s2 y 0 hT, src_def, PhiOp_def, bsrc0, Qop0,
      Gint_zero D hsF, Iop_zero D F hsF, hH, hX]; ring
  have ed4 : ∀ y ∈ Icc (0:ℝ) 1, F 3 y 0 = D.h 3 y + D.q 2 y * F 1 y 0 + D.q 3 y * F 2 y 0 := by
    intro y hy
    have hT : (y, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
    obtain ⟨hsF, hX⟩ := edge3_at D hy
    have hH : H D 3 y 0 = D.h 3 y := congrArg (D.h 3) hX
    rw [hfix 3 y 0 hT, s1 y 0 hT, s2 y 0 hT, src_def, PhiOp_def, bsrc3, Qop3,
      Gint_zero D hsF, Iop_zero D F hsF, hH, hX]; ring
  have i0 : ∀ x ξ, (x, ξ) ∈ Tri → F 0 x ξ =
      F 0 (charX D 0 x ξ 0) (charXi D 0 x ξ 0) + Gint D 0 x ξ + Iop D F 0 x ξ := by
    intro x ξ hx
    obtain ⟨hxi, hy⟩ := foot0 D hx
    have hT' : (charX D 0 x ξ 0, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
    have hH : H D 0 x ξ = D.h 0 (charX D 0 x ξ 0) := rfl
    rw [hxi, ed1 _ hy, s1 _ _ hT', s2 _ _ hT', hfix 0 x ξ hx, src_def, PhiOp_def, bsrc0, Qop0, hH]
    ring
  have i3 : ∀ x ξ, (x, ξ) ∈ Tri → F 3 x ξ =
      F 3 (charX D 3 x ξ 0) (charXi D 3 x ξ 0) + Gint D 3 x ξ + Iop D F 3 x ξ := by
    intro x ξ hx
    obtain ⟨hxi, hy⟩ := foot3 D hx
    have hT' : (charX D 3 x ξ 0, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
    have hH : H D 3 x ξ = D.h 3 (charX D 3 x ξ 0) := rfl
    rw [hxi, ed4 _ hy, s1 _ _ hT', s2 _ _ hT', hfix 3 x ξ hx, src_def, PhiOp_def, bsrc3, Qop3, hH]
    ring
  have i1 : ∀ x ξ, (x, ξ) ∈ Tri → F 1 x ξ =
      F 1 (charX D 1 x ξ 0) (charXi D 1 x ξ 0) + Gint D 1 x ξ + Iop D F 1 x ξ := by
    intro x ξ hx
    obtain ⟨hX, hXi, hst⟩ := diag1_pt D hx
    have hH : H D 1 x ξ = D.h 1 (charX D 1 x ξ 0) := rfl
    rw [s1 x ξ hx, hH, hX, hXi, dg1 _ hst]
  have i2 : ∀ x ξ, (x, ξ) ∈ Tri → F 2 x ξ =
      F 2 (charX D 2 x ξ 0) (charXi D 2 x ξ 0) + Gint D 2 x ξ + Iop D F 2 x ξ := by
    intro x ξ hx
    obtain ⟨hX, hXi, hst⟩ := diag2_pt D hx
    have hH : H D 2 x ξ = D.h 2 (charX D 2 x ξ 0) := rfl
    rw [s2 x ξ hx, hH, hX, hXi, dg2 _ hst]
  refine ⟨?_, ed1, dg1, dg2, ed4⟩
  intro j x ξ hx
  fin_cases j
  · exact i0 x ξ hx
  · exact i1 x ξ hx
  · exact i2 x ξ hx
  · exact i3 x ξ hx

/-! ### Characteristic solution ⇒ fixed-point form -/

lemma char_fix {F : Fin 4 → ℝ → ℝ → ℝ} (hc : IsCharSolution D F) :
    ∀ j x ξ, (x, ξ) ∈ Tri → F j x ξ = src D j x ξ + PhiOp D F j x ξ := by
  have t1 : ∀ x ξ, (x, ξ) ∈ Tri → F 1 x ξ = H D 1 x ξ + Gint D 1 x ξ + Iop D F 1 x ξ := by
    intro x ξ hx
    obtain ⟨hX, hXi, hst⟩ := diag1_pt D hx
    have h := hc.integral 1 x ξ hx
    rw [hX, hXi, hc.diagonal2 _ hst] at h
    have hH : H D 1 x ξ = D.h 1 (charX D 1 x ξ 0) := rfl
    rw [hH, hX]; exact h
  have t2 : ∀ x ξ, (x, ξ) ∈ Tri → F 2 x ξ = H D 2 x ξ + Gint D 2 x ξ + Iop D F 2 x ξ := by
    intro x ξ hx
    obtain ⟨hX, hXi, hst⟩ := diag2_pt D hx
    have h := hc.integral 2 x ξ hx
    rw [hX, hXi, hc.diagonal3 _ hst] at h
    have hH : H D 2 x ξ = D.h 2 (charX D 2 x ξ 0) := rfl
    rw [hH, hX]; exact h
  have f1 : ∀ x ξ, (x, ξ) ∈ Tri → F 1 x ξ = src D 1 x ξ + PhiOp D F 1 x ξ := by
    intro x ξ hx
    rw [t1 x ξ hx, src_def, PhiOp_def, bsrcZ D (by decide) (by decide),
      QopZ D F (by decide) (by decide)]; ring
  have f2 : ∀ x ξ, (x, ξ) ∈ Tri → F 2 x ξ = src D 2 x ξ + PhiOp D F 2 x ξ := by
    intro x ξ hx
    rw [t2 x ξ hx, src_def, PhiOp_def, bsrcZ D (by decide) (by decide),
      QopZ D F (by decide) (by decide)]; ring
  have f0 : ∀ x ξ, (x, ξ) ∈ Tri → F 0 x ξ = src D 0 x ξ + PhiOp D F 0 x ξ := by
    intro x ξ hx
    obtain ⟨hxi, hy⟩ := foot0 D hx
    have hT' : (charX D 0 x ξ 0, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
    have h := hc.integral 0 x ξ hx
    rw [hxi, hc.edge1 _ hy, t1 _ _ hT', t2 _ _ hT'] at h
    have hH : H D 0 x ξ = D.h 0 (charX D 0 x ξ 0) := rfl
    rw [h, src_def, PhiOp_def, bsrc0, Qop0, hH]; ring
  have f3 : ∀ x ξ, (x, ξ) ∈ Tri → F 3 x ξ = src D 3 x ξ + PhiOp D F 3 x ξ := by
    intro x ξ hx
    obtain ⟨hxi, hy⟩ := foot3 D hx
    have hT' : (charX D 3 x ξ 0, (0:ℝ)) ∈ Tri := ⟨le_rfl, hy.1, hy.2⟩
    have h := hc.integral 3 x ξ hx
    rw [hxi, hc.edge4 _ hy, t1 _ _ hT', t2 _ _ hT'] at h
    have hH : H D 3 x ξ = D.h 3 (charX D 3 x ξ 0) := rfl
    rw [h, src_def, PhiOp_def, bsrc3, Qop3, hH]; ring
  intro j x ξ hx
  fin_cases j
  · exact f0 x ξ hx
  · exact f1 x ξ hx
  · exact f2 x ξ hx
  · exact f3 x ξ hx

/-! ### The contraction estimate for `Φ` -/

lemma PhiOp_diff {F F' : Fin 4 → ℝ → ℝ → ℝ}
    (hF : ∀ i, ContinuousOn (fun p : ℝ × ℝ => F i p.1 p.2) Tri)
    (hF' : ∀ i, ContinuousOn (fun p : ℝ × ℝ => F' i p.1 p.2) Tri)
    {Cm M L qm : ℝ} (hL : 0 < L) (hCm0 : 0 ≤ Cm) (hM0 : 0 ≤ M) (hqm0 : 0 ≤ qm)
    (hCm : ∀ j i y η, (y, η) ∈ Tri → |D.Cc j i y η| ≤ Cm)
    (hM : ∀ i y η, (y, η) ∈ Tri → |F i y η - F' i y η| ≤ M * Real.exp (L * E3 D y))
    (hq : ∀ k y, y ∈ Icc (0:ℝ) 1 → |D.q k y| ≤ qm)
    (j : Fin 4) {x ξ : ℝ} (hx : (x, ξ) ∈ Tri) :
    |PhiOp D F j x ξ - PhiOp D F' j x ξ| ≤
      (1 + 2 * qm) * (4 * (Cm * M * Real.exp (L * E3 D x) / L)) := by
  have hT0 : 0 ≤ 4 * (Cm * M * Real.exp (L * E3 D x) / L) := by
    have := mul_nonneg (mul_nonneg hCm0 hM0) (Real.exp_pos (L * E3 D x)).le
    have := div_nonneg this hL.le
    linarith
  have hI := Iop_diff D hF hF' hL hCm0 hM0 hCm hM j (p := (x, ξ)) hx
  have hedge : ∀ j' k, |Iop D F k (charX D j' x ξ 0) 0 - Iop D F' k (charX D j' x ξ 0) 0| ≤
      4 * (Cm * M * Real.exp (L * E3 D x) / L) ∧ ∀ m, |D.q m (charX D j' x ξ 0)| ≤ qm := by
    intro j' k
    obtain ⟨h1, -, h3, h5⟩ := x0f D j' hx
    obtain ⟨a, b, c⟩ := h3
    have hT' : (charX D j' x ξ 0, (0:ℝ)) ∈ Tri := by rw [h1]; exact ⟨le_rfl, a.trans b, c⟩
    refine ⟨?_, fun m => hq m _ (by rw [h1]; exact ⟨a.trans b, c⟩)⟩
    refine (Iop_diff D hF hF' hL hCm0 hM0 hCm hM k (p := (charX D j' x ξ 0, 0)) hT').trans ?_
    have hE : E3 D (charX D j' x ξ 0) ≤ E3 D x := by rw [h1]; exact (E3 D).monotone h5
    have he : Real.exp (L * E3 D (charX D j' x ξ 0)) ≤ Real.exp (L * E3 D x) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hE hL.le)
    have hCM : 0 ≤ Cm * M := mul_nonneg hCm0 hM0
    have h6 := mul_le_mul_of_nonneg_left he hCM
    have h7 := div_le_div_of_nonneg_right h6 hL.le
    show 4 * (Cm * M * Real.exp (L * E3 D (charX D j' x ξ 0)) / L) ≤ _
    linarith
  by_cases h0 : j = 0
  · subst h0
    obtain ⟨e1, q1⟩ := hedge 0 1
    obtain ⟨e2, -⟩ := hedge 0 2
    rw [PhiOp_def, PhiOp_def, Qop0, Qop0]
    have hA := abs_mul (D.q 0 (charX D 0 x ξ 0))
      (Iop D F 1 (charX D 0 x ξ 0) 0 - Iop D F' 1 (charX D 0 x ξ 0) 0)
    have hB := abs_mul (D.q 1 (charX D 0 x ξ 0))
      (Iop D F 2 (charX D 0 x ξ 0) 0 - Iop D F' 2 (charX D 0 x ξ 0) 0)
    have hA' := mul_le_mul (q1 0) e1 (abs_nonneg _) hqm0
    have hB' := mul_le_mul (q1 1) e2 (abs_nonneg _) hqm0
    have h3 := abs_add_three
      (D.q 0 (charX D 0 x ξ 0) * (Iop D F 1 (charX D 0 x ξ 0) 0 - Iop D F' 1 (charX D 0 x ξ 0) 0))
      (D.q 1 (charX D 0 x ξ 0) * (Iop D F 2 (charX D 0 x ξ 0) 0 - Iop D F' 2 (charX D 0 x ξ 0) 0))
      (Iop D F 0 x ξ - Iop D F' 0 x ξ)
    have e : D.q 0 (charX D 0 x ξ 0) * Iop D F 1 (charX D 0 x ξ 0) 0 +
          D.q 1 (charX D 0 x ξ 0) * Iop D F 2 (charX D 0 x ξ 0) 0 + Iop D F 0 x ξ -
        (D.q 0 (charX D 0 x ξ 0) * Iop D F' 1 (charX D 0 x ξ 0) 0 +
          D.q 1 (charX D 0 x ξ 0) * Iop D F' 2 (charX D 0 x ξ 0) 0 + Iop D F' 0 x ξ) =
        D.q 0 (charX D 0 x ξ 0) * (Iop D F 1 (charX D 0 x ξ 0) 0 - Iop D F' 1 (charX D 0 x ξ 0) 0) +
        D.q 1 (charX D 0 x ξ 0) * (Iop D F 2 (charX D 0 x ξ 0) 0 - Iop D F' 2 (charX D 0 x ξ 0) 0) +
        (Iop D F 0 x ξ - Iop D F' 0 x ξ) := by ring
    rw [e]
    nlinarith
  by_cases h3 : j = 3
  · subst h3
    obtain ⟨e1, q1⟩ := hedge 3 1
    obtain ⟨e2, -⟩ := hedge 3 2
    rw [PhiOp_def, PhiOp_def, Qop3, Qop3]
    have hA := abs_mul (D.q 2 (charX D 3 x ξ 0))
      (Iop D F 1 (charX D 3 x ξ 0) 0 - Iop D F' 1 (charX D 3 x ξ 0) 0)
    have hB := abs_mul (D.q 3 (charX D 3 x ξ 0))
      (Iop D F 2 (charX D 3 x ξ 0) 0 - Iop D F' 2 (charX D 3 x ξ 0) 0)
    have hA' := mul_le_mul (q1 2) e1 (abs_nonneg _) hqm0
    have hB' := mul_le_mul (q1 3) e2 (abs_nonneg _) hqm0
    have h3 := abs_add_three
      (D.q 2 (charX D 3 x ξ 0) * (Iop D F 1 (charX D 3 x ξ 0) 0 - Iop D F' 1 (charX D 3 x ξ 0) 0))
      (D.q 3 (charX D 3 x ξ 0) * (Iop D F 2 (charX D 3 x ξ 0) 0 - Iop D F' 2 (charX D 3 x ξ 0) 0))
      (Iop D F 3 x ξ - Iop D F' 3 x ξ)
    have e : D.q 2 (charX D 3 x ξ 0) * Iop D F 1 (charX D 3 x ξ 0) 0 +
          D.q 3 (charX D 3 x ξ 0) * Iop D F 2 (charX D 3 x ξ 0) 0 + Iop D F 3 x ξ -
        (D.q 2 (charX D 3 x ξ 0) * Iop D F' 1 (charX D 3 x ξ 0) 0 +
          D.q 3 (charX D 3 x ξ 0) * Iop D F' 2 (charX D 3 x ξ 0) 0 + Iop D F' 3 x ξ) =
        D.q 2 (charX D 3 x ξ 0) * (Iop D F 1 (charX D 3 x ξ 0) 0 - Iop D F' 1 (charX D 3 x ξ 0) 0) +
        D.q 3 (charX D 3 x ξ 0) * (Iop D F 2 (charX D 3 x ξ 0) 0 - Iop D F' 2 (charX D 3 x ξ 0) 0) +
        (Iop D F 3 x ξ - Iop D F' 3 x ξ) := by ring
    rw [e]
    nlinarith
  rw [PhiOp_def, PhiOp_def, QopZ D F h0 h3, QopZ D F' h0 h3, zero_add, zero_add]
  have : 4 * (Cm * M * Real.exp (L * E3 D x) / L) ≤
      (1 + 2 * qm) * (4 * (Cm * M * Real.exp (L * E3 D x) / L)) := by nlinarith
  exact hI.trans this

/-! ### Compactness bounds -/

lemma tri_compact : IsCompact Tri := by
  have hcl : IsClosed Tri := by
    have h1 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
    have h2 : IsClosed {p : ℝ × ℝ | p.2 ≤ p.1} := isClosed_le continuous_snd continuous_fst
    have h3 : IsClosed {p : ℝ × ℝ | p.1 ≤ 1} := isClosed_le continuous_fst continuous_const
    exact h1.inter (h2.inter h3)
  refine ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0:ℝ)) (b := 1))).of_isClosed_subset hcl ?_
  intro p hp
  obtain ⟨h0, h1, h2⟩ := hp
  exact ⟨⟨h0.trans h1, h2⟩, ⟨h0, h1.trans h2⟩⟩

lemma Cbound : ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ j i y η, (y, η) ∈ Tri → |D.Cc j i y η| ≤ Cm := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => (fun j i => D.Cc j i p.1 p.2 : Fin 4 → Fin 4 → ℝ)) Tri :=
    continuousOn_pi.2 fun j => continuousOn_pi.2 fun i => D.Cc_cont j i
  obtain ⟨C, hC⟩ := tri_compact.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun j i y η h => ?_⟩
  have h1 := hC (y, η) h
  have h2 : ‖D.Cc j i y η‖ ≤ ‖(fun j i => D.Cc j i y η : Fin 4 → Fin 4 → ℝ)‖ :=
    (norm_le_pi_norm (fun i => D.Cc j i y η) i).trans
      (norm_le_pi_norm (fun j i => D.Cc j i y η : Fin 4 → Fin 4 → ℝ) j)
  rw [Real.norm_eq_abs] at h2
  exact (h2.trans h1).trans (le_max_left _ _)

lemma qbound : ∃ qm : ℝ, 0 ≤ qm ∧ ∀ k y, y ∈ Icc (0:ℝ) 1 → |D.q k y| ≤ qm := by
  have hc : ContinuousOn (fun y : ℝ => (fun k => D.q k y : Fin 4 → ℝ)) (Icc 0 1) :=
    continuousOn_pi.2 fun k => D.q_cont k
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun k y h => ?_⟩
  have h1 := hC y h
  have h2 : ‖D.q k y‖ ≤ ‖(fun k => D.q k y : Fin 4 → ℝ)‖ := norm_le_pi_norm (fun k => D.q k y) k
  rw [Real.norm_eq_abs] at h2
  exact (h2.trans h1).trans (le_max_left _ _)

lemma E3_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ E3 D y := by
  rw [← E3_zero D]; exact (E3 D).monotone hy

end D4

end HBK

namespace HBK

set_option maxHeartbeats 1000000 in
theorem main (D : GoursatData) :
    (∃ F : Fin 4 → ℝ → ℝ → ℝ,
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) Tri) ∧
        IsCharSolution D F) ∧
    (∀ F F' : Fin 4 → ℝ → ℝ → ℝ,
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) Tri) →
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F' j p.1 p.2) Tri) →
      IsCharSolution D F → IsCharSolution D F' →
      ∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri → F j x ξ = F' j x ξ) := by
  obtain ⟨Cm, hCm0, hCm⟩ := Cbound D
  obtain ⟨qm, hqm0, hqm⟩ := qbound D
  set L : ℝ := 8 * (1 + 2 * qm) * Cm + 1 with hLdef
  have hL : 0 < L := by
    have : 0 ≤ (1 + 2 * qm) * Cm := mul_nonneg (by linarith) hCm0
    rw [hLdef]; nlinarith
  have core : ∀ F F' : Fin 4 → ℝ → ℝ → ℝ,
      (∀ i, ContinuousOn (fun p : ℝ × ℝ => F i p.1 p.2) Tri) →
      (∀ i, ContinuousOn (fun p : ℝ × ℝ => F' i p.1 p.2) Tri) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ i y η, (y, η) ∈ Tri → |F i y η - F' i y η| ≤ M * Real.exp (L * E3 D y)) →
      ∀ j x ξ, (x, ξ) ∈ Tri →
        |PhiOp D F j x ξ - PhiOp D F' j x ξ| ≤ (1 / 2) * (M * Real.exp (L * E3 D x)) := by
    intro F F' hF hF' M hM0 hM j x ξ hx
    have h := PhiOp_diff D hF hF' hL hCm0 hM0 hqm0 hCm hM hqm j hx
    have hA : 0 ≤ M * Real.exp (L * E3 D x) := mul_nonneg hM0 (Real.exp_pos _).le
    have hc : 0 ≤ (1 + 2 * qm) * Cm := mul_nonneg (by linarith) hCm0
    refine h.trans ?_
    have e : (1 + 2 * qm) * (4 * (Cm * M * Real.exp (L * E3 D x) / L)) =
        (4 * ((1 + 2 * qm) * Cm) / L) * (M * Real.exp (L * E3 D x)) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hA
    rw [div_le_iff₀ hL, hLdef]
    nlinarith
  refine ⟨?_, ?_⟩
  · -- existence via the contraction principle
    haveI : CompactSpace Tri := isCompact_iff_compactSpace.mp tri_compact
    let rT : ℝ × ℝ → Tri := fun p => ⟨rr p, rr_mem p⟩
    have hrT : Continuous rT := continuous_rr.subtype_mk _
    let ext : C(Tri, Fin 4 → ℝ) → Fin 4 → ℝ → ℝ → ℝ :=
      fun G j x ξ => Real.exp (L * E3 D x) * G (rT (x, ξ)) j
    have hext : ∀ G j, Continuous (fun p : ℝ × ℝ => ext G j p.1 p.2) := by
      intro G j
      have h1 : Continuous (fun p : ℝ × ℝ => G (rT p) j) :=
        (continuous_apply j).comp (G.continuous.comp hrT)
      have h2 : Continuous (fun p : ℝ × ℝ => Real.exp (L * E3 D p.1)) :=
        Real.continuous_exp.comp (continuous_const.mul ((E3_cont D).comp continuous_fst))
      exact h2.mul h1
    let T : C(Tri, Fin 4 → ℝ) → C(Tri, Fin 4 → ℝ) := fun G =>
      ⟨fun p j => Real.exp (-(L * E3 D p.1.1)) *
          (src D j p.1.1 p.1.2 + PhiOp D (ext G) j p.1.1 p.1.2), by
        apply continuous_pi
        intro j
        have h1 : Continuous (fun p : Tri => src D j p.1.1 p.1.2) :=
          (src_contOn D j).comp_continuous continuous_subtype_val (fun p => p.2)
        have h2 : Continuous (fun p : Tri => PhiOp D (ext G) j p.1.1 p.1.2) :=
          (PhiOp_contOn D (fun i => (hext G i).continuousOn) j).comp_continuous
            continuous_subtype_val (fun p => p.2)
        have h3 : Continuous (fun p : Tri => Real.exp (-(L * E3 D p.1.1))) :=
          Real.continuous_exp.comp ((continuous_const.mul
            ((E3_cont D).comp (continuous_fst.comp continuous_subtype_val))).neg)
        exact h3.mul (h1.add h2)⟩
    have hT : ∀ G G' : C(Tri, Fin 4 → ℝ), dist (T G) (T G') ≤ (1 / 2) * dist G G' := by
      intro G G'
      have hd0 : 0 ≤ dist G G' := dist_nonneg
      rw [ContinuousMap.dist_le (by positivity)]
      intro p
      rw [dist_pi_le_iff (by positivity)]
      intro j
      have hM : ∀ i y η, (y, η) ∈ Tri →
          |ext G i y η - ext G' i y η| ≤ dist G G' * Real.exp (L * E3 D y) := by
        intro i y η _
        show |Real.exp (L * E3 D y) * G (rT (y, η)) i - Real.exp (L * E3 D y) * G' (rT (y, η)) i|
          ≤ _
        rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have := (dist_le_pi_dist (G (rT (y, η))) (G' (rT (y, η))) i).trans
          (ContinuousMap.dist_apply_le_dist (rT (y, η)))
        rwa [Real.dist_eq] at this
      have hk := core (ext G) (ext G') (fun i => (hext G i).continuousOn)
        (fun i => (hext G' i).continuousOn) (dist G G') hd0 hM j p.1.1 p.1.2 p.2
      show dist (Real.exp (-(L * E3 D p.1.1)) *
          (src D j p.1.1 p.1.2 + PhiOp D (ext G) j p.1.1 p.1.2))
        (Real.exp (-(L * E3 D p.1.1)) *
          (src D j p.1.1 p.1.2 + PhiOp D (ext G') j p.1.1 p.1.2)) ≤ 1 / 2 * dist G G'
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
      have e : src D j p.1.1 p.1.2 + PhiOp D (ext G) j p.1.1 p.1.2 -
          (src D j p.1.1 p.1.2 + PhiOp D (ext G') j p.1.1 p.1.2) =
          PhiOp D (ext G) j p.1.1 p.1.2 - PhiOp D (ext G') j p.1.1 p.1.2 := by ring
      rw [e]
      have hee : Real.exp (-(L * E3 D p.1.1)) * Real.exp (L * E3 D p.1.1) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-(L * E3 D p.1.1)) *
            |PhiOp D (ext G) j p.1.1 p.1.2 - PhiOp D (ext G') j p.1.1 p.1.2|
          ≤ Real.exp (-(L * E3 D p.1.1)) * (1 / 2 * (dist G G' * Real.exp (L * E3 D p.1.1))) :=
            mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
        _ = 1 / 2 * dist G G' * (Real.exp (-(L * E3 D p.1.1)) * Real.exp (L * E3 D p.1.1)) := by
            ring
        _ = 1 / 2 * dist G G' := by rw [hee, mul_one]
    have hK : ContractingWith (1 / 2 : NNReal) T := by
      constructor
      · rw [← NNReal.coe_lt_coe]; push_cast; norm_num
      · exact LipschitzWith.of_dist_le_mul fun G G' => by push_cast; exact hT G G'
    have hfp := ContractingWith.fixedPoint_isFixedPt (f := T) hK
    refine ⟨ext (ContractingWith.fixedPoint T hK),
      fun j => (hext _ j).continuousOn, fix_char D ?_⟩
    intro j x ξ hx
    have h2 : rT (x, ξ) = ⟨(x, ξ), hx⟩ := Subtype.ext (rr_eq hx)
    have h1 : (T (ContractingWith.fixedPoint T hK)) (rT (x, ξ)) j =
        (ContractingWith.fixedPoint T hK) (rT (x, ξ)) j := by
      rw [hfp.eq]
    show Real.exp (L * E3 D x) * (ContractingWith.fixedPoint T hK) (rT (x, ξ)) j = _
    rw [← h1, h2]
    show Real.exp (L * E3 D x) * (Real.exp (-(L * E3 D x)) *
      (src D j x ξ + PhiOp D (ext (ContractingWith.fixedPoint T hK)) j x ξ)) = _
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  · -- uniqueness
    intro F F' hF hF' hc hc' j x ξ hx
    have hfixF := char_fix D hc
    have hfixF' := char_fix D hc'
    have hdiff : ContinuousOn
        (fun p : ℝ × ℝ => (fun i => F i p.1 p.2 - F' i p.1 p.2 : Fin 4 → ℝ)) Tri :=
      continuousOn_pi.2 fun i => (hF i).sub (hF' i)
    obtain ⟨M0, hM0⟩ := tri_compact.exists_bound_of_continuousOn hdiff
    have hstart : ∀ i y η, (y, η) ∈ Tri →
        |F i y η - F' i y η| ≤ max M0 0 * Real.exp (L * E3 D y) := by
      intro i y η h
      have h1 : |F i y η - F' i y η| ≤ M0 := by
        have := (norm_le_pi_norm (fun i => F i y η - F' i y η) i).trans (hM0 (y, η) h)
        rwa [Real.norm_eq_abs] at this
      obtain ⟨a, b, c⟩ := h
      have h2 : 1 ≤ Real.exp (L * E3 D y) :=
        Real.one_le_exp (mul_nonneg hL.le (E3_nonneg D (a.trans b)))
      calc |F i y η - F' i y η| ≤ max M0 0 := h1.trans (le_max_left _ _)
        _ = max M0 0 * 1 := (mul_one _).symm
        _ ≤ max M0 0 * Real.exp (L * E3 D y) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    have hiter : ∀ n : ℕ, ∀ i y η, (y, η) ∈ Tri →
        |F i y η - F' i y η| ≤ (max M0 0 * (1 / 2) ^ n) * Real.exp (L * E3 D y) := by
      intro n
      induction n with
      | zero => simpa using hstart
      | succ n ih =>
        intro i y η h
        have hk := core F F' hF hF' (max M0 0 * (1 / 2) ^ n)
          (mul_nonneg (le_max_right _ _) (by positivity)) ih i y η h
        rw [hfixF i y η h, hfixF' i y η h]
        have e : src D i y η + PhiOp D F i y η - (src D i y η + PhiOp D F' i y η) =
            PhiOp D F i y η - PhiOp D F' i y η := by ring
        rw [e]
        calc |PhiOp D F i y η - PhiOp D F' i y η|
            ≤ 1 / 2 * (max M0 0 * (1 / 2) ^ n * Real.exp (L * E3 D y)) := hk
          _ = max M0 0 * (1 / 2) ^ (n + 1) * Real.exp (L * E3 D y) := by ring
    have hlim : Tendsto (fun n : ℕ => max M0 0 * (1 / 2 : ℝ) ^ n * Real.exp (L * E3 D x))
        atTop (𝓝 0) := by
      have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
      have h := (h0.const_mul (max M0 0)).mul_const (Real.exp (L * E3 D x))
      rw [mul_zero, zero_mul] at h
      exact h
    have hle : |F j x ξ - F' j x ξ| ≤ 0 := ge_of_tendsto' hlim (fun n => hiter n j x ξ hx)
    have := abs_nonpos_iff.1 hle
    linarith

end HBK

open HyperbolicBackstepping.Kernel in
theorem solution (D : GoursatData) :
    (∃ F : Fin 4 → ℝ → ℝ → ℝ,
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) Tri) ∧
        IsCharSolution D F) ∧
    (∀ F F' : Fin 4 → ℝ → ℝ → ℝ,
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F j p.1 p.2) Tri) →
      (∀ j, ContinuousOn (fun p : ℝ × ℝ => F' j p.1 p.2) Tri) →
      IsCharSolution D F → IsCharSolution D F' →
      ∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri → F j x ξ = F' j x ξ) := by
  exact HBK.main D

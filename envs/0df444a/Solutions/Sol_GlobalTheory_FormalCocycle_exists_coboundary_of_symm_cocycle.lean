-- Prove2me | solution 1 for GlobalTheory.FormalCocycle.exists_coboundary_of_symm_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:39.846635+00:00
-- url     : https://prove2.me/submissions/04608fc8-d0c9-46d8-91e8-6dc91c9dfab5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
import Theorems.Thm_GlobalTheory_FormalCocycle_cen2
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_zero
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_X
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_add
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_pts
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt3
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_zero_pt
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_addAt
import Theorems.Thm_GlobalTheory_FormalCocycle_cen_mapAt
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_mapAt
import Theorems.Thm_GlobalTheory_FormalCocycle_mapAt_zero
import Theorems.Thm_GlobalTheory_FormalCocycle_mapAt_mapAt
import Theorems.Thm_GlobalTheory_FormalCocycle_mapAt_addAt
import Theorems.Thm_GlobalTheory_FormalCocycle_formalSeriesSubstPoints_standard_three
import Theorems.Thm_GlobalTheory_FormalCocycle_axis_at
import Theorems.Thm_GlobalTheory_FormalCocycle_symm_at
import Theorems.Thm_GlobalTheory_FormalCocycle_cocycle_at
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_elim2
import Theorems.Thm_GlobalTheory_FormalCocycle_hasSubst_elim3
import Theorems.Thm_GlobalTheory_FormalCocycle_subst_elim2
import Theorems.Thm_GlobalTheory_FormalCalc_existsUnique_coboundary_param
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst
import Theorems.Thm_GlobalTheory_FormalCalc_subst_elim_elim_X
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
open GlobalTheory GlobalTheory.FormalCocycle
namespace GlobalTheory.FormalCocycle
theorem _root_.solution :
    LogSt → (∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) → IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by
  intro hlog hinv k _ _ d G c hax hsy hco
  obtain ⟨ℓ, hℓ, hlin, hadd⟩ := hlog k d G
  obtain ⟨e, -, he, hle, hel⟩ := hinv k d ℓ hℓ (by rw [hlin, Matrix.det_one]; exact isUnit_one)
  have hF := G.const
  have hexp : ∀ {μ : Type} {u v : Fin d → MvPowerSeries μ k}, Cen u → Cen v →
      addAt G.F (mapAt e u) (mapAt e v) = mapAt e (u + v) := by
    intro μ u v hu hv
    have h1 := mapAt_addAt hℓ hF hadd (cen_mapAt he hu) (cen_mapAt he hv)
    rw [mapAt_mapAt he hle hu, mapAt_mapAt he hle hv] at h1
    rw [← h1, mapAt_mapAt hℓ hel (cen_addAt hF (cen_mapAt he hu) (cen_mapAt he hv))]
  obtain ⟨B, hB⟩ : ∃ B : MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) k,
      ∀ {μ : Type} {u v t : Fin d → MvPowerSeries μ k}, Cen u → Cen v → Cen t →
        subst (Sum.elim u (Sum.elim v t)) B = evAt ![mapAt e u, mapAt e v, t] c := by
    refine ⟨evAt ![mapAt e fun i => X (inl i), mapAt e fun i => X (inr (inl i)),
      fun i => X (inr (inr i))] c, ?_⟩
    intro μ u v t hu hv ht
    have hb := hasSubst_elim3 hu hv ht
    rw [subst_evAt3 hb (cen_mapAt he (cen_X _)) (cen_mapAt he (cen_X _)) (cen_X _),
      subst_mapAt hb e (cen_X _), subst_mapAt hb e (cen_X _)]
    simp only [subst_X hb, elim_inl, elim_inr]
  have hBX : B = evAt ![mapAt e fun i => X (inl i), mapAt e fun i => X (inr (inl i)),
      fun i => X (inr (inr i))] c := by
    rw [← hB (cen_X _) (cen_X _) (cen_X _), GlobalTheory.FormalCalc.subst_elim_elim_X]
  obtain ⟨K, ⟨hK0, hK1, hK⟩, -⟩ := GlobalTheory.FormalCalc.existsUnique_coboundary_param (B := B)
    (by
      have h1 := hB (μ := Fin d) (u := 0) (v := 0) (t := X) cen_zero cen_zero (cen_X id)
      rw [mapAt_zero he] at h1
      exact h1.trans (axis_at hax cen_zero (cen_X id)))
    (by
      rw [hB (cen_X _) (cen_X _) (cen_X _)]
      conv_rhs => rw [hBX]
      exact symm_at hsy (cen_mapAt he (cen_X _)) (cen_mapAt he (cen_X _)) (cen_X _))
    (by
      rw [hB (cen_X _) (cen_X _) (cen_X _), hB (cen_X _) (cen_X _) (cen_X _)]
      have h1 := hB (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d)
        (cen_add (cen_X fun i => inl i) (cen_X fun i => inr (inl i)))
        (cen_X fun i => inr (inr (inl i))) (cen_X fun i => inr (inr (inr i)))
      have h2 := hB (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d) (cen_X fun i => inl i)
        (cen_add (cen_X fun i => inr (inl i)) (cen_X fun i => inr (inr (inl i))))
        (cen_X fun i => inr (inr (inr i)))
      rw [← hexp (cen_X _) (cen_X _)] at h1 h2
      have h3 := cocycle_at hF hco (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d)
        (cen_mapAt he (cen_X fun i => inl i)) (cen_mapAt he (cen_X fun i => inr (inl i)))
        (cen_mapAt he (cen_X fun i => inr (inr (inl i)))) (cen_X fun i => inr (inr (inr i)))
      rw [← h1, ← h2] at h3
      exact h3)
  have hp : ∀ {n : ℕ} (j : Fin n), Cen (pt k d j) := cen_pt
  have hev : ∀ {n : ℕ} {u t : Pt k n d} (L : MvPowerSeries (Fin d ⊕ Fin d) k), Cen u → Cen t →
      ev ![u, t] (subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) L) =
        subst (Sum.elim (mapAt ℓ u) t) L := by
    intro n u t L hu ht
    have ha := cen2 hu ht
    have hb := hasSubst_pts ha
    rw [ev, subst_elim2 hb (cen_mapAt hℓ (hp 0)) (hp 1), subst_mapAt hb ℓ (hp 0), subst_pt ha,
      subst_pt ha]
    rfl
  have hzero : ∀ L : MvPowerSeries (Fin d ⊕ Fin d) k,
      subst (Sum.elim (fun _ => 0) X : Fin d ⊕ Fin d → MvPowerSeries (Fin d) k) L = 0 →
      ev (n := 1) ![0, pt k d 0]
        (subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) L) = 0 := by
    intro L hL
    rw [hev L cen_zero (hp 0), mapAt_zero hℓ]
    have hb : HasSubst (pt k (n := 1) d 0) := hasSubst_of_constantCoeff_zero (hp 0)
    have h1 := subst_elim2 hb (u := 0) (t := X) cen_zero (cen_X id) L
    rw [subst_zero_pt hb] at h1
    simp only [subst_X hb] at h1
    refine h1.symm.trans ?_
    exact (congrArg _ hL).trans (GlobalTheory.FormalCalc.subst_zero' hb)
  have hneg : ∀ {m n : ℕ} {a : Fin m → Pt k n d}, (∀ j, Cen (a j)) → ∀ f : PS k m d,
      ev a (-f) = - ev a f := by
    intro m n a ha f
    unfold ev
    rw [← coe_substAlgHom (hasSubst_pts ha), map_neg]
  refine ⟨-subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) K, ?_, fun i => ?_, ?_⟩
  · rw [hneg (cen2 cen_zero (hp 0)), hzero K hK0, neg_zero]
  · have hb := hasSubst_pts (cen2 (cen_zero (μ := Fin 1 × Fin d)) (hp 0))
    rw [map_neg, hneg (cen2 cen_zero (hp 0)), neg_eq_zero,
      GlobalTheory.FormalCalc.pderiv_subst (hasSubst_elim2 (cen_mapAt hℓ (hp 0)) (hp 1)), Fintype.sum_sum_type]
    have h2 : ∀ j : Fin d, pderiv k ((0 : Fin 2), i) (pt k (n := 2) d 1 j) = 0 := fun j =>
      pderiv_X_of_ne (by simp)
    simp only [elim_inl, elim_inr, h2, mul_zero, Finset.sum_const_zero, add_zero]
    rw [ev, GlobalTheory.FormalCalc.subst_sum' hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h3 := hzero _ (hK1 j)
    rw [ev] at h3
    rw [subst_mul hb, h3, zero_mul]
  · have hA : Cen (addOf G.F (pt k (n := 3) d 0) (pt k d 1)) := cen_addAt hF (hp 0) (hp 1)
    rw [hneg (cen2 (hp 0) (hp 2)), hneg (cen2 (hp 1) (hp 2)), hneg (cen2 hA (hp 2)),
      hev K (hp 0) (hp 2), hev K (hp 1) (hp 2), hev K hA (hp 2)]
    have hl0 := cen_mapAt hℓ (hp (n := 3) 0)
    have hl1 := cen_mapAt hℓ (hp (n := 3) 1)
    have hb := hasSubst_elim3 hl0 hl1 (hp 2)
    have h1 := hB hl0 hl1 (hp 2)
    rw [mapAt_mapAt hℓ hel (hp 0), mapAt_mapAt hℓ hel (hp 1), formalSeriesSubstPoints_standard_three, hK, subst_sub hb,
      subst_sub hb, subst_elim2 hb (fun _ => by simp) (cen_X _), subst_elim2 hb (cen_X _) (cen_X _),
      subst_elim2 hb (cen_X _) (cen_X _)] at h1
    simp only [subst_add hb, subst_X hb, elim_inl, elim_inr] at h1
    have h4 : mapAt ℓ (addOf G.F (pt k (n := 3) d 0) (pt k d 1)) =
        fun i => mapAt ℓ (pt k (n := 3) d 0) i + mapAt ℓ (pt k (n := 3) d 1) i :=
      mapAt_addAt hℓ hF hadd (hp 0) (hp 1)
    rw [h4, ← h1]
    ring
end GlobalTheory.FormalCocycle

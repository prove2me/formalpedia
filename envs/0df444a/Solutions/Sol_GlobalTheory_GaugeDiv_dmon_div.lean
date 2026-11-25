-- Prove2me | solution 1 for GlobalTheory.GaugeDiv.dmon_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:33.329963+00:00
-- url     : https://prove2.me/submissions/d2668ea1-4bf2-4701-8439-1cb17f08ee1d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_add
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_sub
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_natCast_mul
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_int
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_ev_self
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_ev_ne
import Theorems.Thm_GlobalTheory_GaugeDiv_dof_graph
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_axis
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_zero_sub
import Theorems.Thm_GlobalTheory_GaugeDiv_dd_one_sub
import Theorems.Thm_GlobalTheory_GaugeDiv_dof_al
import Theorems.Thm_GlobalTheory_GaugeDiv_dof_dy
import Theorems.Thm_GlobalTheory_GaugeInt_IP_gp
import Theorems.Thm_GlobalTheory_GaugeInt_int_const
import Theorems.Thm_GlobalTheory_GaugeInt_int_ev
import Theorems.Thm_GlobalTheory_GaugeInt_ip1
import Theorems.Thm_GlobalTheory_GaugeInt_ip_pt
import Theorems.Thm_GlobalTheory_QuadDeriv_hX0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
namespace GlobalTheory.GaugeDiv
theorem _root_.solution {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (h1 : ev (n := 1) ![pt k d 0, 0] g = 0)
    (c1 : ∀ s, constantCoeff (pderiv k s g) = 0)
    (hl : DI φ (defL F g)) (hr : DI φ (defR F g)) {ι : Type} [Fintype ι] (U V : ι → Fin d → k)
    (hu : ∀ l i, U l i ∈ φ.range) (hv : ∀ l i, V l i ∈ φ.range) (N : ℕ)
    (huv : ∀ l i, lin (U l) (w i) = N * V l i)
    (hβ : ∀ l l', dotProduct (U l) ((bilinPart k g).mulVec (V l')) ∈ φ.range) (m : ι →₀ ℕ) :
    ∃ r : R, constantCoeff (DmonOf F U m (ev (n := 1) ![pt k d 0, w] g)) = φ (N * r) := by
  have hF := iF.gp
  have hV := pair_points_zero_constant (gp_pt (k := k) (d := d) (n := 1) 0) hw
  let S : PS k 2 d → Prop := fun G => constantCoeff G ∈ φ.range ∧
    ∀ l, DD F 0 (U l) G ∈ IntS φ 2 d ∧ DD F 1 (V l) G ∈ IntS φ 2 d
  have hS : ∀ G ∈ IntS φ 2 d, S G := fun G hG =>
    ⟨int_const hG, fun l => ⟨dd_int iF 0 (hu l) hG, dd_int iF 1 (hv l) hG⟩⟩
  have cD : ∀ a v, constantCoeff (DD F a v g) ∈ φ.range := fun a v => by
    simp only [DD, map_sum, map_mul, c1, mul_zero, Finset.sum_const_zero]
    exact zero_mem _
  have hS0 : ∀ l, S (DD F 0 (U l) g) := by
    intro l
    have h := dd_zero_sub iF hU g hl (hu l)
    refine ⟨cD _ _, fun l' => ⟨?_, ?_⟩⟩
    · have h' := dd_int iF 0 (hu l') h
      rwa [dd_sub, dd_ev_ne F (by decide), sub_zero] at h'
    · have h' := add_mem (dd_int iF 1 (hv l') h)
        (int_ev (ip1 (ip_pt (n := 2) 1)) (dof_al iF hU g hr (hu l) (hv l') (hβ l l')))
      rwa [dd_sub, dd_ev_self, sub_add_cancel] at h'
  have hS1 : ∀ l, S (DD F 1 (V l) g) := by
    intro l
    have h := dd_one_sub iF hU g hr (hv l)
    refine ⟨cD _ _, fun l' => ⟨?_, ?_⟩⟩
    · have h' := add_mem (dd_int iF 0 (hu l') h)
        (int_ev (ip1 (ip_pt (n := 2) 0)) (dof_dy iF hU g hl (hu l') (hv l) (hβ l' l)))
      rwa [dd_sub, dd_ev_self, sub_add_cancel] at h'
    · have h' := dd_int iF 1 (hv l') h
      rwa [dd_sub, dd_ev_ne F (by decide), sub_zero] at h'
  let P : PS k 1 d → Prop := fun f => f = ev (n := 1) ![pt k d 0, w] g ∨
    ∃ A E, S A ∧ S E ∧ ev (n := 1) ![pt k d 0, 0] A = 0 ∧
      f = ev (n := 1) ![pt k d 0, w] (A + N * E)
  have hstep : ∀ l f, P f → P (Dof F (U l) f) := by
    rintro l f (rfl | ⟨A, E, hA, hE, h0, rfl⟩)
    · exact Or.inr ⟨_, _, hS0 l, hS1 l, dd_axis hF hU _ h1, dof_graph hF hU hw hom _ _ N (huv l) g⟩
    · refine Or.inr ⟨DD F 0 (U l) A, DD F 0 (U l) E + DD F 1 (V l) A + N * DD F 1 (V l) E,
        hS _ (hA.2 l).1, hS _ (add_mem (add_mem (hE.2 l).1 (hA.2 l).2)
          (mul_mem (natCast_mem _ N) (hE.2 l).2)), dd_axis hF hU _ h0, ?_⟩
      rw [dof_graph hF hU hw hom _ _ N (huv l), dd_add, dd_add, dd_natCast_mul, dd_natCast_mul]
      congr 1
      ring
  have hP : P (DmonOf F U m (ev (n := 1) ![pt k d 0, w] g)) := by
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => exact Or.inl rfl
    | cons a L ih => exact Function.Iterate.rec P ih (hstep a) (m a)
  rcases hP with e | ⟨A, E, -, ⟨⟨r, hr⟩, -⟩, h0, e⟩
  · refine ⟨0, ?_⟩
    rw [e, gt_const_ev_eq _ hV, ← gt_const_ev_eq _ hX0, h1]
    simp
  · refine ⟨r, ?_⟩
    rw [e, gt_const_ev_eq _ hV, map_add, ← gt_const_ev_eq _ hX0 A, h0]
    simp [hr]
end GlobalTheory.GaugeDiv

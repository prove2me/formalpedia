-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:09:31.170672+00:00
-- url     : https://prove2.me/submissions/1bf7cece-02b3-470d-b911-0aa7674528ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_dualMap_comp
import Theorems.Thm_GlobalTheory_SqZero_res_res
import Theorems.Thm_GlobalTheory_SqZero_scl_scl
import Theorems.Thm_GlobalTheory_SqZero_res_scl
import Theorems.Thm_GlobalTheory_SqZero_exists_res_eq_of_unitInChart
import Theorems.Thm_GlobalTheory_SqZero_scl_pow_eq_of_le
import Theorems.Thm_GlobalTheory_SqZero_dual_ext
import Theorems.Thm_GlobalTheory_SqZero_exists_scl_eq
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_IsAway_swap
import Theorems.Thm_GlobalTheory_SqZero_agree_of_isAway
import Theorems.Thm_GlobalTheory_SqZero_away_ext
import Theorems.Thm_GlobalTheory_SqZero_away_glue
import Theorems.Thm_GlobalTheory_SqZero_exists_fin_unitInChart
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_SqZero_span_range_map
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable [Smooth G.hom] {ρ : S →ₐ[R] S'} {g : S}
namespace GlobalTheory.SqZero
theorem _root_.solution (hρ : IsAway ρ g)
    {w' : sp (R₀ := R) (DualNumber S') ⟶ G} (hw' : IsTanOver w') :
    ∃ (N : ℕ) (w : sp (R₀ := R) (DualNumber S) ⟶ G), IsTanOver w ∧
      res ρ w = scl (ρ g ^ N) w' := by
  obtain ⟨κ, _, s, hs, hU⟩ := exists_fin_unitInChart G S
  have := Fintype.ofFinite κ
  let q : ∀ k, S →ₐ[R] Localization.Away (s k) := fun k => awayHom R (s k)
  have hq : ∀ k, IsAway (q k) (s k) := fun k => isAway_awayHom (s k)
  let p : ∀ k, Localization.Away (s k) →ₐ[R] Localization.Away (q k g) := fun k => awayHom R (q k g)
  have hp : ∀ k, IsAway (p k) (q k g) := fun k => isAway_awayHom (q k g)
  have hψ0 : ∀ k, ∃ ψ : S' →ₐ[R] Localization.Away (q k g), ψ.comp ρ = (p k).comp (q k) :=
    fun k => hρ.lift _ (hp k).unit
  choose ψ hψ using hψ0
  have hψa : ∀ k, IsAway (ψ k) (ρ (s k)) := fun k => hρ.swap (hq k) (hψ k) (hp k)
  have hgk : ∀ k, ψ k (ρ g) = p k (q k g) := fun k => by
    rw [← AlgHom.comp_apply, hψ k, AlgHom.comp_apply]
  have hk : ∀ k, ∃ (N : ℕ) (v : sp (R₀ := R) (DualNumber (Localization.Away (s k))) ⟶ G),
      IsTanOver v ∧ res (p k) v = scl (p k (q k g) ^ N) (res (ψ k) w') :=
    fun k => exists_res_eq_of_unitInChart (hU k) (hp k) (hw'.res (ψ k))
  choose N v hv hvN using hk
  obtain ⟨M, hM⟩ : ∃ M, ∀ k, N k ≤ M := ⟨Finset.univ.sup N, fun k => Finset.le_sup (Finset.mem_univ k)⟩
  let W' := scl (ρ g ^ M) w'
  let v1 : ∀ k, sp (R₀ := R) (DualNumber (Localization.Away (s k))) ⟶ G :=
    fun k => scl (q k g ^ (M - N k)) (v k)
  have H1 : ∀ k, res (p k) (v1 k) = res (ψ k) W' := fun k => by
    simp only [v1, W']
    rw [res_scl, hvN k, scl_scl, res_scl, map_pow, map_pow, hgk, ← pow_add,
      Nat.sub_add_cancel (hM k)]
  let q2 : ∀ k l, S →ₐ[R] Localization.Away (s k * s l) := fun k l => awayHom R (s k * s l)
  have hq2 : ∀ k l, IsAway (q2 k l) (s k * s l) := fun k l => isAway_awayHom _
  have hja0 : ∀ k l, ∃ ja : Localization.Away (s k) →ₐ[R] Localization.Away (s k * s l),
      ja.comp (q k) = q2 k l := fun k l => (hq k).lift _
    (isUnit_of_mul_isUnit_left (y := q2 k l (s l)) (by rw [← map_mul]; exact (hq2 k l).unit))
  have hjb0 : ∀ k l, ∃ ja : Localization.Away (s l) →ₐ[R] Localization.Away (s k * s l),
      ja.comp (q l) = q2 k l := fun k l => (hq l).lift _
    (isUnit_of_mul_isUnit_right (x := q2 k l (s k)) (by rw [← map_mul]; exact (hq2 k l).unit))
  choose ja hja using hja0
  choose jb hjb using hjb0
  have hP : ∀ k l, ∃ P : ℕ,
      scl (q2 k l g ^ P) (res (ja k l) (v1 k)) = scl (q2 k l g ^ P) (res (jb k l) (v1 l)) := by
    intro k l
    have hp2 := isAway_awayHom (R := R) (q2 k l g)
    obtain ⟨χ, hχ⟩ := (hp k).lift ((awayHom R (q2 k l g)).comp (ja k l)) (by
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply (ja k l), hja]
      exact hp2.unit)
    obtain ⟨χ', hχ'⟩ := (hp l).lift ((awayHom R (q2 k l g)).comp (jb k l)) (by
      rw [AlgHom.comp_apply, ← AlgHom.comp_apply (jb k l), hjb]
      exact hp2.unit)
    have e : χ.comp (ψ k) = χ'.comp (ψ l) := hρ.ext (by
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hψ, hψ, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
        hχ, hχ', AlgHom.comp_assoc, AlgHom.comp_assoc, hja, hjb])
    refine exists_scl_eq hp2 (((hv k).scl _).res _) (((hv l).scl _).res _) ?_
    rw [res_res, res_res, ← hχ, ← hχ', ← res_res, ← res_res, H1, H1, res_res, res_res, e]
  choose Q hQ using hP
  obtain ⟨P, hPQ⟩ : ∃ P, ∀ k l, Q k l ≤ P :=
    ⟨Finset.univ.sup fun k => Finset.univ.sup (Q k), fun k l =>
      (Finset.le_sup (f := Q k) (Finset.mem_univ l)).trans
        (Finset.le_sup (f := fun k => Finset.univ.sup (Q k)) (Finset.mem_univ k))⟩
  let v2 : ∀ k, sp (R₀ := R) (DualNumber (Localization.Away (s k))) ⟶ G :=
    fun k => scl (q k g ^ P) (v1 k)
  have H2 : ∀ k l, res (ja k l) (v2 k) = res (jb k l) (v2 l) := fun k l => by
    show res (ja k l) (scl (q k g ^ P) (v1 k)) = res (jb k l) (scl (q l g ^ P) (v1 l))
    rw [res_scl (ja k l) (q k g ^ P) (v1 k), res_scl (jb k l) (q l g ^ P) (v1 l), map_pow, map_pow, ← AlgHom.comp_apply (ja k l), hja,
      ← AlgHom.comp_apply (jb k l), hjb]
    exact scl_pow_eq_of_le (hPQ k l) (hQ k l)
  obtain ⟨z, hz⟩ := away_glue (X := G) (span_range_map hs (inlS R S)) (fun k => dualMap (q k))
    (fun k => (hq k).dualMap) v2 (fun k l T _ _ a b e =>
      agree_of_isAway ((hq k).dualMap) ((hq l).dualMap) (a₀ := dualMap (ja k l))
        (b₀ := dualMap (jb k l)) (by rw [dualMap_comp, dualMap_comp, hja, hjb])
        (by rw [dualMap_comp, hja, ← map_mul]; exact (hq2 k l).dualMap) (H2 k l) T a b e)
  refine ⟨M + P, z, ?_, ?_⟩
  · show spMap (fstS R S) ≫ z = 1
    refine away_ext hs q hq fun k => ?_
    rw [comp_one', ← Category.assoc, spMap_comp, ← fstS_comp_dualMap, ← spMap_comp, Category.assoc,
      hz k]
    exact ((hv k).scl _).scl _
  · refine dual_ext (span_range_map hs ρ) ψ hψa fun k => ?_
    rw [res_res, hψ k, ← res_res]
    show res (p k) (spMap (dualMap (q k)) ≫ z) = _
    rw [hz k]
    show res (p k) (scl (q k g ^ P) (v1 k)) = _
    rw [res_scl (p k) (q k g ^ P) (v1 k), H1 k]
    simp only [W']
    rw [res_scl, res_scl, scl_scl]
    simp only [map_pow, hgk]
    rw [← pow_add, add_comm]
end GlobalTheory.SqZero

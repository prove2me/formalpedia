-- Prove2me | solution 1 for GlobalTheory.Published.SvN.exists_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:45.201839+00:00
-- url     : https://prove2.me/submissions/00427b3b-94d2-4552-91b8-9da0246a3c22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_Splits_comp
import Theorems.Thm_GlobalTheory_Published_SvN_exists_selfDual
import Theorems.Thm_GlobalTheory_Published_SvN_exists_splits
import Theorems.Thm_GlobalTheory_Published_SvN_finite_quot
import Theorems.Thm_GlobalTheory_Published_SvN_isCompact_int
import Theorems.Thm_GlobalTheory_Published_SvN_exists_ne_zero
import Theorems.Thm_GlobalTheory_Published_SvN_eventually_psi
import Theorems.Thm_P2M_GlobalTheory_Published_SvN_eventually_psi__9e5e2c7b09ad
import Theorems.Thm_GlobalTheory_Published_SvN_psi_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {W : Type} [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}
variable [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
namespace GlobalTheory.Published.SvN
theorem _root_.solution (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) (hn : B.Nondegenerate) {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ (A : AddSubgroup W) (α : W → ℂ), Splits (fun x y => ψ (B x y / 2)) A α ∧ (alt_psi hB ψ).perp A ≤ A ∧
      (∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1) ∧
      (∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A)) ∧
      ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1 := by
  classical
  have := IsModuleTopology.topologicalAddGroup F W
  have := IsModuleTopology.toContinuousSMul (R := F) (A := W)
  set h := alt_psi hB ψ
  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ1 (AddChar.ext _ _ hc)
  have ht0 : t₀ ≠ 0 := by rintro rfl; simp at ht₀
  let b := Module.finBasis F W
  let b' := B.dualBasis hn b
  have hcB : Continuous fun p : W × W => B p.1 p.2 := IsModuleTopology.continuous_bilinear_of_finite_left B
  have hcw : ∀ w, Continuous fun u => B u w := fun w => hcB.comp (f := fun u => (u, w)) (by fun_prop)
  let K : Set W := b'.equivFun.symm '' Set.pi Set.univ fun _ => (𝒪[F] : Set F)
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_int).image
    (IsModuleTopology.continuous_of_linearMap b'.equivFun.symm.toLinearMap)
  let T : F → Set W := fun s => {t | ∃ i, ∃ o ∈ 𝒪[F], t = (s * o) • b i}
  have hmem : ∀ s x, x ∈ h.perp (T s) ↔ ∀ i, ∀ o ∈ 𝒪[F], ψ (o * (s * B x (b i))) = 1 := by
    intro s x
    have e : ∀ i o, ψ (B x ((s * o) • b i) / 2) ^ 2 = ψ (o * (s * B x (b i))) := fun i o => by
      rw [psi_sq h2, map_smul, smul_eq_mul]; congr 1; ring
    constructor
    · intro hx i o ho
      rw [← e]; exact hx _ ⟨i, o, ho, rfl⟩
    · rintro hx _ ⟨i, o, ho, rfl⟩
      exact (e i o).trans (hx i o ho)
  have fA : ∀ r, r ≠ 0 → ∀ x ∈ h.perp (T (t₀ / r)), ∃ y ∈ K, x = r • y := by
    intro r hr x hx
    refine ⟨r⁻¹ • x, ⟨fun i => r⁻¹ * B x (b i), fun i _ => ?_, ?_⟩, by rw [smul_inv_smul₀ hr]⟩
    · by_contra hc
      have hz : r⁻¹ * B x (b i) ≠ 0 := fun h0 => hc (by beta_reduce; rw [h0]; exact zero_mem _)
      have hi : (r⁻¹ * B x (b i))⁻¹ ∈ 𝒪[F] := ((valuation F).valuationSubring.mem_or_inv_mem _).resolve_left hc
      have := (hmem _ x).1 hx i _ hi
      apply ht₀
      rw [← this]; congr 1
      have := right_ne_zero_of_mul hz
      field_simp
    · rw [LinearEquiv.symm_apply_eq]
      funext i
      simp [b']
  have fB : ∀ s, (h.perp (T s) : Set W) ∈ 𝓝 0 := by
    intro s
    have : ∀ᶠ x in 𝓝 (0 : W), ∀ i, ∀ o ∈ 𝒪[F], ψ (o * (s * B x (b i))) = 1 := by
      refine eventually_all.2 fun i => ?_
      have hc : Continuous fun x => s * B x (b i) := continuous_const.mul (hcw _)
      exact (hc.tendsto' 0 0 (by simp)).eventually (eventually_psi hψ)
    filter_upwards [this] with x hx using (hmem s x).2 hx
  have fC : ∀ N ∈ 𝓝 (0 : W), ∀ C, IsCompact C → ∃ r : F, r ≠ 0 ∧ ∀ y ∈ C, r • y ∈ N := by
    intro N hN C hC
    refine exists_ne_zero (hC.eventually_forall_of_forall_eventually fun y _ => ?_)
    exact (continuous_smul.tendsto' ((0 : F), y) 0 (by simp)).eventually hN
  obtain ⟨r, hr, hrK⟩ : ∃ r : F, r ≠ 0 ∧ ∀ p ∈ K ×ˢ K, ψ (r * r * B p.1 p.2 / 2) = 1 := by
    refine exists_ne_zero ((hK.prod hK).eventually_forall_of_forall_eventually fun p _ => ?_)
    have hc : Continuous fun z : F × W × W => z.1 * z.1 * B z.2.1 z.2.2 / 2 :=
      ((continuous_fst.mul continuous_fst).mul (hcB.comp continuous_snd)).div_const 2
    exact (hc.tendsto' (0, p) 0 (by simp)).eventually (eventually_psi' hψ)
  set L := h.perp (T (t₀ / r))
  have hL : ∀ x ∈ L, ∀ y ∈ L, ψ (B x y / 2) = 1 := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := fA r hr x hx
    obtain ⟨y', hy', rfl⟩ := fA r hr y hy
    rw [← hrK (x', y') ⟨hx', hy'⟩]; congr 2; simp; ring
  obtain ⟨A, hLA, hA, hA'⟩ := exists_selfDual h L fun x hx y hy => by simp only [hL x hx y hy, one_pow]
  obtain ⟨α, hα, hαL⟩ := exists_splits h hLA hL hA
  obtain ⟨s, hs, hsL⟩ := fC _ (fB (t₀ / r)) (⋃ i, (fun o : F => o • b i) '' (𝒪[F] : Set F))
    (isCompact_iUnion fun i => isCompact_int.image (by fun_prop))
  have hAK : (A : Set W) ⊆ (fun y => (t₀ / s) • y) '' K := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := fA (t₀ / s) (div_ne_zero ht0 hs) a (by
      rintro _ ⟨i, o, ho, rfl⟩
      refine hA ha _ (hLA ?_)
      rw [div_div_cancel₀ ht0, mul_smul]
      exact hsL _ (Set.mem_iUnion.2 ⟨i, o, ho, rfl⟩))
    exact ⟨y, hy, rfl⟩
  refine ⟨A, α, hα, hA', ?_, fun N hN => ?_, fun w => ?_⟩
  · filter_upwards [fB (t₀ / r)] with u hu using ⟨hLA hu, hαL u hu⟩
  · obtain ⟨q, hq, hqN⟩ := fC N hN K hK
    refine ⟨T (t₀ / q), fun x hx => ?_, finite_quot A _ (fB _) (hK.image (by fun_prop)) hAK⟩
    obtain ⟨y, hy, rfl⟩ := fA q hq x hx
    exact hqN y hy
  · filter_upwards [((hcw w).tendsto' 0 0 (by simp)).eventually (eventually_psi' hψ)] with u hu
    rw [psi_sq h2, hu]
end GlobalTheory.Published.SvN

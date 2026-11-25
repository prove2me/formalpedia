-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:44.272539+00:00
-- url     : https://prove2.me/submissions/9b544708-edaa-4022-94cd-cc4ddaaf3cfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_nondeg
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_dual_latIn
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_idx_swap
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_idx_map_dvd
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_idx_mul
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_latIn_le
import Theorems.Thm_GlobalTheory_Mass_PrimDisc_gens_swap
import Theorems.Thm_GlobalTheory_T_hermitianLatticeDiscriminantOrder_ne_zero_unimodular
import Theorems.Thm_GlobalTheory_T_lattice_quotient_gens_and_intermediate_count
import Theorems.Thm_GlobalTheory_T_witt_extension_totally_definite_hermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.PrimDisc
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L U e hL ⟨t, hte, ht⟩
  obtain ⟨hc, hsU, hpU, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 (perp h U)
  set W := perp h U with hW
  have horth : ∀ (u : U) (w : W), h (u : V) (w : V) = 0 := fun u w => by
    have := w.2
    simp only [hW, perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this u u.2
  have horth' : ∀ (u : U) (w : W), h (w : V) (u : V) = 0 := fun u w => by
    rw [← hs.eq, horth, map_zero]
  let p : V →ₗ[K] U := U.projectionOnto W hc
  let q : V →ₗ[K] W := W.projectionOnto U hc.symm
  have hpq : ∀ x, (p x : V) + q x = x := Submodule.projection_add_projection_eq_self hc
  have hp1 : ∀ a : U, p a = a := Submodule.projectionOnto_apply_left hc
  have hq1 : ∀ a : W, q a = a := Submodule.projectionOnto_apply_left hc.symm
  obtain ⟨iU, dU⟩ := dual_latIn h hs hp U hsU hpU p (Submodule.projectionOnto_surjective hc)
    (fun x a => by conv_rhs => rw [← hpq x, map_add, LinearMap.add_apply, horth', add_zero]) L hL
  obtain ⟨iW, dW⟩ := dual_latIn h hs hp W hsW hpW q (Submodule.projectionOnto_surjective hc.symm)
    (fun x a => by conv_rhs => rw [← hpq x, map_add, LinearMap.add_apply, horth, zero_add]) L hL
  have hLd : L ≤ dual h L := by rw [ht]; exact le_sup_left
  have nL := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs (nondeg h hp) L hL).1
  have nU := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K U _ hK hsU (nondeg _ hpU) _ iU).1
  have mU := idx_mul _ _ _ (latIn_le U p hp1 L) (Submodule.map_mono hLd)
  have mW := idx_mul _ _ _ (latIn_le W q hq1 L) (Submodule.map_mono hLd)
  have sw := idx_swap U W p q hpq L
  have dvU : idxN (L.map (q.restrictScalars (𝓞 K))) (latIn W L) ∣ discN (hRes h U) (latIn U L) := by
    rw [discN, dU, ← mU, sw]
    exact dvd_mul_right _ _
  refine ⟨iU, iW, ?_, ?_⟩
  · rw [discN, dW, ← mW]
    exact Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero nU) dvU)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero nL) (idx_map_dvd W q L _))
  · obtain ⟨s, hs1, hs2⟩ := (GlobalTheory.T.lattice_quotient_gens_and_intermediate_count K W _ _ (latIn_le W q hq1 L)
      (ne_zero_of_dvd_ne_zero nU dvU)).1 (hL.1.fg.map _)
    obtain ⟨s', h1, h2⟩ := gens_swap U W p q hp1 hpq L s hs2
    refine ⟨s' ∪ t.image p, (Finset.card_union_le _ _).trans
      (Nat.add_le_add (h1.trans hs1) (Finset.card_image_le.trans hte)), ?_⟩
    rw [dU, ht, Submodule.map_sup, h2, Submodule.map_span, Finset.coe_union, Submodule.span_union,
      sup_assoc, Finset.coe_image]
    rfl
end GlobalTheory.Mass.PrimDisc

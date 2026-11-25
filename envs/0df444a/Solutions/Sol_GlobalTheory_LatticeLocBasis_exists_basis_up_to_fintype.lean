-- Prove2me | solution 1 for GlobalTheory.LatticeLocBasis.exists_basis_up_to_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:07.807949+00:00
-- url     : https://prove2.me/submissions/0dc6b549-532e-4b71-9f40-ee71b181e55c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMatrixBasisLatticeUpToDenominatorNotMem

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
open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors
open GlobalTheory GlobalTheory.LatticeLocBasis
namespace GlobalTheory.LatticeLocBasis
theorem _root_.solution {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (n → E) := Submodule.span A (L : Set (n → E)) with hM
  have : Submodule.IsLattice E M :=
    { fg := by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = Fintype.card n := by
    simpa using Submodule.IsLattice.finrank_of_pi E M
  let c : Basis n A M := (Module.finBasisOfFinrankEq A M hrk).reindex (Fintype.equivFin n).symm
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis n A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : n → E) = (t i : O) • (c i : n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : n → n → E := fun i => (c' i : n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
end GlobalTheory.LatticeLocBasis

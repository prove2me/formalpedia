-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:51.543421+00:00
-- url     : https://prove2.me/submissions/edb9761a-c87b-46b9-900f-f62736f42bff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_invol_eq_pow
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_exists_ring
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_val_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
namespace GlobalTheory.UnitLemma.UnrExt
theorem _root_.solution : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by
  intro K d hd
  choose c0 hc0 using K.c_int
  have hi := IsFractionRing.injective K.O K.E
  let c : K.O →+* K.O :=
    { toFun := c0
      map_one' := hi (by rw [← hc0]; simp)
      map_mul' := fun x y => hi (by rw [map_mul, ← hc0, ← hc0, ← hc0]; simp)
      map_zero' := hi (by rw [← hc0]; simp)
      map_add' := fun x y => hi (by rw [map_add, ← hc0, ← hc0, ← hc0]; simp) }
  have hc : ∀ x, K.c (algebraMap K.O K.E x) = algebraMap K.O K.E (c x) := hc0
  have hcc : ∀ x, c (c x) = x := fun x => hi (by rw [← hc, ← hc, K.c_c])
  let ce : K.O ≃+* K.O := RingEquiv.ofRingHom c c (RingHom.ext hcc) (RingHom.ext hcc)
  let s := ResidueField.mapEquiv ce
  have hs : ∀ x, s (residue K.O x) = residue K.O (c x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField K.O)
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField K.O) p⟩
  obtain ⟨⟨f, hf⟩, hsq⟩ := invol_eq_pow p K.card_res s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hcc]) (by
    obtain ⟨x, y, hxy, hn⟩ := K.c_res
    refine ⟨residue K.O x, fun h => hn ?_⟩
    rw [hs] at h
    rw [← residue_eq_zero_iff, map_sub, ← hi ((hc x).symm.trans hxy), h, sub_self])
  obtain ⟨W, _, _, _, _, _, _, c', z, hfin, hinj, hirr, hrk, hcard, hinv, hca, hres, hz, hadj⟩ :=
    exists_ring K.O p K.card_res hf hd c hcc (fun x => by rw [← hs, hsq])
  let L := FractionRing W
  have hiW := IsFractionRing.injective W L
  have hj : Function.Injective ((algebraMap W L).comp (algebraMap K.O W)) := hiW.comp hinj
  let φ : K.E →+* L := IsFractionRing.lift hj
  have hφ : ∀ x, φ (algebraMap K.O K.E x) = algebraMap W L (algebraMap K.O W x) :=
    IsFractionRing.lift_algebraMap hj
  haveI : CharZero L := charZero_of_injective_ringHom φ.injective
  let ce' : W ≃+* W := RingEquiv.ofRingHom c' c' (RingHom.ext hinv) (RingHom.ext hinv)
  let cL : L ≃+* L := IsFractionRing.ringEquivOfRingEquiv ce'
  have hcL : ∀ y, cL (algebraMap W L y) = algebraMap W L (c' y) := fun y =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ce' y
  letI : Algebra K.E L := φ.toAlgebra
  haveI : IsScalarTower K.O K.E L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K.O W L]; exact (hφ x).symm
  refine ⟨{ O := W, E := L, c := cL
            c_c := fun x => ?_
            c_int := fun x => ⟨c' x, hcL x⟩
            c_res := ⟨z, c' z, hcL z, hres⟩
            q := K.q ^ d
            card_res := hcard }, φ, rfl, fun x => ?_, val_map (algebraMap K.O W) hirr φ hφ, fun h => ?_, ?_,
    algebraMap W L z, hz.map_of_injective hiW, ?_⟩
  · obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    simp only [map_div₀, hcL, hinv]
  · obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K.O) x
    simp only [map_div₀, hc, hφ, hcL, hca]
  · have := IsUnit.map (algebraMap K.O W) h
    rwa [map_ofNat] at this
  · exact (IsFractionRing.finrank_eq K.O K.E W L).trans hrk
  · have hint : IsIntegral K.E (algebraMap W L z) :=
      ((IsIntegral.of_finite K.O z).map (IsScalarTower.toAlgHom K.O W L)).tower_top
    have hmem : ∀ y : W, algebraMap W L y ∈ IntermediateField.adjoin K.E {algebraMap W L z} := fun y => by
      have hy : y ∈ Algebra.adjoin K.O {z} := hadj ▸ Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain rfl : x = z := hx
        exact IntermediateField.mem_adjoin_simple_self _ _
      | algebraMap r => rw [← hφ]; exact IntermediateField.algebraMap_mem _ _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    show Algebra.adjoin K.E {algebraMap W L z} = ⊤
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    exact IntermediateField.div_mem _ (hmem a) (hmem b)
end GlobalTheory.UnitLemma.UnrExt

-- Prove2me | solution 1 for GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:22.876077+00:00
-- url     : https://prove2.me/submissions/f2fc3801-a202-4571-847e-742ffc111eaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_nsmul_integral_mem_nhds
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.OpenLat
variable (F : Type) [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.OpenLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  intro F E _ _ _ _ _ n L hL
  classical
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  haveI : ContinuousSMul (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.toContinuousSMul _ _
  refine ⟨fun N hN => ?_, fun W hW => ?_⟩
  · let S : AddSubgroup (Fin n → RA F E) := (hat F (L : Set (Fin n → E))).map (nsmulAddMonoidHom N)
    have hS : {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y} = S := by
      ext z
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩
    rw [hS]
    refine S.isOpen_of_mem_nhds (g := 0) ?_
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    let b := Module.finBasis F E
    let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
    choose d hd hdL using fun i k => exists_denom L hL (Pi.single i (b k))
    have hn : ∀ᶠ z : Fin n → RA F E in 𝓝 0, ∀ i k, ∃ a : FiniteAdeleRing (𝓞 F) F,
        (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ B.repr (z i) k = (N * d i k) • a := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro k
      have hc : Continuous fun z : Fin n → RA F E => B.coord k (z i) :=
        (IsModuleTopology.continuous_of_linearMap (B.coord k)).comp (continuous_apply i)
      have := nsmul_integral_mem_nhds F (N * d i k) (Nat.mul_pos hN (hd i k))
      have h0 : B.coord k ((0 : Fin n → RA F E) i) = 0 := map_zero _
      exact hc.continuousAt.preimage_mem_nhds (x := 0) (h0 ▸ this)
    refine Filter.mem_of_superset hn fun z hz => ?_
    choose a ha hza using hz
    refine ⟨∑ i, ∑ k, fun j => a i k ⊗ₜ[F] (d i k • (Pi.single i (b k) : Fin n → E)) j,
      sum_mem fun i _ => sum_mem fun k _ =>
        AddSubgroup.subset_closure ⟨a i k, ha i k, _, hdL i k, rfl⟩, ?_⟩
    funext j
    rw [nsmulAddMonoidHom_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Finset.sum_apply, ← B.sum_repr (z j), Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hza, Algebra.TensorProduct.basis_apply, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul,
        smul_smul, smul_assoc]
      congr 1
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · intro i _ hij
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij.symm, smul_zero, TensorProduct.tmul_zero]
    · simp
  · let w := RingOfIntegers.basis E
    let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → FiniteAdeleRing (𝓞 F) F) → RA F E :=
      fun c => ∑ k, c k • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] algebraMap (𝓞 E) E (w k))
    have hφ : Continuous φ := continuous_finset_sum _ fun k _ => by fun_prop
    have h0 : φ 0 = 0 := by simp [φ]
    have h1 : φ ⁻¹' W ∈ 𝓝 0 := hφ.continuousAt.preimage_mem_nhds (h0 ▸ hW)
    rw [nhds_pi, Filter.mem_pi] at h1
    obtain ⟨I, -, t, ht, hsub⟩ := h1
    obtain ⟨N, hN, hNt⟩ := exists_nsmul_adele F (⋂ k, t k) (Filter.iInter_mem.mpr ht)
    refine ⟨N, hN, fun y hy => ?_⟩
    have hex : ∃ c, (∀ k v, c k v ∈ v.adicCompletionIntegers F) ∧ φ c = y := by
      induction hy using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hx
        refine ⟨fun k => w.repr x k • a, fun k v => zsmul_mem (ha v) _, ?_⟩
        conv_rhs => rw [← w.sum_repr x, map_sum, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_zsmul, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul']
      | zero => exact ⟨0, fun k v => zero_mem _, h0⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hc, rfl⟩ := hx
        obtain ⟨e, he, rfl⟩ := hy
        exact ⟨c + e, fun k v => add_mem (hc k v) (he k v), by simp [φ, add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact ⟨-c, fun k v => neg_mem (hc k v), by simp [φ]⟩
    obtain ⟨c, hc, rfl⟩ := hex
    have h2 : N • φ c = φ (N • c) := by
      simp only [φ, Finset.smul_sum, Pi.smul_apply, smul_assoc]
    rw [h2]
    exact hsub fun k _ => Set.mem_iInter.mp (hNt (c k) (hc k)) k
end GlobalTheory.AdLat.OpenLat

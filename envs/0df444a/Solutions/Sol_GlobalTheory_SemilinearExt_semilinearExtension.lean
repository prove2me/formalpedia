-- Prove2me | solution 1 for GlobalTheory.SemilinearExt.semilinearExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:10:44.906581+00:00
-- url     : https://prove2.me/submissions/b10be0cd-db1c-48be-a3a9-96dd75170d3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor
import Theorems.Thm_GlobalTheory_SemilinearExt_algebraMap_tmul
import Theorems.Thm_GlobalTheory_SemilinearExt_exists_basis_tensor
import Theorems.Thm_GlobalTheory_SemilinearExt_extOfBasis_basis
import Theorems.Thm_GlobalTheory_SemilinearExt_carries_of_basis
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SemilinearExtensionBases_IsExt_apply_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
open GlobalTheory GlobalTheory.SemilinearExt
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
namespace GlobalTheory.SemilinearExt
theorem _root_.solution : SemilinearExtension := by
  intro Ks LL WL _ _ _ _ _ _ _ WK hForm O K K'' _ _ _ _ _ _ _ _ _ _ emb hemb Fm _ _ _ _ eF
  obtain ⟨n, bv, -, hKs, hspanK, hLL, hspanL⟩ := hForm
  let B : Basis (Fin n) LL WL := Basis.mk hLL hspanL.ge
  have hB : ∀ k, B k = bv k := fun k => Basis.mk_apply _ _ _
  let BK : Basis (Fin n) Ks WK := (Basis.span hKs).map (LinearEquiv.ofEq _ _ hspanK)
  have hBK : ∀ k, (BK k : WL) = bv k := fun k => by simp [BK, Basis.span_apply]
  let bF : Basis (Fin n) K Fm := (Algebra.TensorProduct.basis K BK).map eF.symm
  obtain ⟨c, hc⟩ := exists_basis_tensor (O := O) (K'' := K'') bF
  have hck : ∀ k, c k = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [hc, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  have hscal : ∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m) := by
    intro a m
    rw [← RingHom.comp_apply emb (algebraMap Ks LL) a, hemb, RingHom.comp_apply, algebraMap_tmul]
  have hf : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) →
      ∀ f : WK, e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
    intro e he f
    have hterm : ∀ (r : Ks) (j : Fin n),
        e (r • bv j) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] (r • BK j)) := by
      intro r j
      rw [← algebraMap_smul LL r (bv j), map_smulₛₗ, he, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        hscal, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have hsum : (f : WL) = ∑ j, BK.repr f j • bv j := by
      conv_lhs => rw [← BK.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBK]
    rw [hsum, map_sum]
    simp_rw [hterm]
    rw [← TensorProduct.tmul_sum, ← map_sum eF.symm, ← TensorProduct.tmul_sum, BK.sum_repr]
  have hext : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → IsExt O emb eF e := by
    intro e he ι _ a f
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hf e he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hval : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e →
      ∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := by
    intro e he k
    rw [← hBK]
    exact he.apply_coe (BK k)
  let e₀ : WL →ₛₗ[emb] K'' ⊗[O] Fm :=
    extOfBasis emb B fun k => (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)
  have he₀ : ∀ k, e₀ (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [← hB]
    exact extOfBasis_basis emb B _ k
  refine ⟨⟨e₀, hext e₀ he₀, fun e' he' => B.ext fun k => ?_⟩, fun e he => ?_, fun a m => ?_⟩
  · rw [hB, hval e' he' k, he₀ k]
  · exact fun ι b => carries_of_basis e B c (fun k => by rw [hB, hval e he k, hck k]) b
  · exact hscal a m
end GlobalTheory.SemilinearExt

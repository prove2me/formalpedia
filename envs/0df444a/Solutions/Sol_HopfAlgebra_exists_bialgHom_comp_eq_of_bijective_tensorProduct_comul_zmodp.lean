-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c8454d90-caef-5d9a-9d76-adb5e79d5ec2

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe v

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {Bc : Type v} [CommRing Bc] [HopfAlgebra (ZMod p) Bc] [Module.Finite (ZMod p) Bc]
    {Be : Type v} [CommRing Be] [HopfAlgebra (ZMod p) Be] [Module.Finite (ZMod p) Be]
    (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
    (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe)
    (hker_πe : RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B)
    (hσ : πe.comp σ = BialgHom.id (ZMod p) Be)
    (hunr : Algebra.FormallyUnramified (ZMod p) Be)
    (hker_qc : RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
      Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)))
    (hΘ : ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
      (Coalgebra.comul (R := ZMod p) b))
    (u : B →ₐc[ZMod p] B) :
    ∃ (uc : Bc →ₐc[ZMod p] Bc) (ue : Be →ₐc[ZMod p] Be),
      qc.comp u = uc.comp qc ∧ πe.comp u = ue.comp πe ∧ u.comp σ = σ.comp ue ∧
      ∀ b : B, Θ (u b) = Algebra.TensorProduct.map (uc : Bc →ₐ[ZMod p] Bc) (ue : Be →ₐ[ZMod p] Be) (Θ b) := by
  classical
  haveI := hunr

  let ue : Be →ₐc[ZMod p] Be := πe.comp (u.comp σ)
  have hσ' : ∀ x : Be, πe (σ x) = x := fun x => by
    have := DFunLike.congr_fun hσ x
    simpa using this

  have hnil : ∀ b : B, πe b = 0 → πe (u b) = 0 := by
    intro b hb
    have hb' : b ∈ nilradical B := by
      rw [← hker_πe]; exact hb
    have : u b ∈ nilradical B := by
      rw [mem_nilradical] at hb' ⊢
      obtain ⟨n, hn⟩ := hb'
      exact ⟨n, by rw [← map_pow, hn, map_zero]⟩
    rw [← hker_πe] at this
    exact this

  have h2 : ∀ b : B, πe (u b) = ue (πe b) := by
    intro b
    show πe (u b) = πe (u (σ (πe b)))
    have hdiff : πe (σ (πe b) - b) = 0 := by rw [map_sub, hσ', sub_self]
    have := hnil _ hdiff
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this.symm
  have h2' : πe.comp u = ue.comp πe := by
    apply BialgHom.ext; intro b; simp [h2]

  have hnilp : IsNilpotent (RingHom.ker ((πe : B →ₐ[ZMod p] Be) : B →+* Be)) := by
    have : RingHom.ker ((πe : B →ₐ[ZMod p] Be) : B →+* Be) = nilradical B := hker_πe
    rw [this]
    haveI : IsNoetherianRing B := IsNoetherianRing.of_finite (ZMod p) B
    exact IsNoetherianRing.isNilpotent_nilradical B
  have h3alg : (u : B →ₐ[ZMod p] B).comp (σ : Be →ₐ[ZMod p] B) =
      (σ : Be →ₐ[ZMod p] B).comp (ue : Be →ₐ[ZMod p] Be) := by
    apply Algebra.FormallyUnramified.lift_unique' (πe : B →ₐ[ZMod p] Be) hnilp
    apply AlgHom.ext; intro x
    show πe (u (σ x)) = πe (σ (ue x))
    rw [hσ']
    rfl
  have h3 : ∀ x : Be, u (σ x) = σ (ue x) := fun x => by
    have := DFunLike.congr_fun h3alg x
    simpa using this
  have h3' : u.comp σ = σ.comp ue := by
    apply BialgHom.ext; intro x; simp [h3]

  have hKu : RingHom.ker (qc : B →ₐ[ZMod p] Bc) ≤
      Ideal.comap (u : B →ₐ[ZMod p] B) (RingHom.ker (qc : B →ₐ[ZMod p] Bc)) := by
    rw [hker_qc, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    rw [show (u : B →ₐ[ZMod p] B) ((σ : Be →ₐ[ZMod p] B) x) = (σ : Be →ₐ[ZMod p] B) (ue x) from h3 x]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker] at hx ⊢
    change Coalgebra.counit (ue x) = 0
    change Coalgebra.counit x = 0 at hx
    rw [CoalgHomClass.counit_comp_apply]; exact hx

  let K : Ideal B := RingHom.ker (qc : B →ₐ[ZMod p] Bc)
  have hqc' : Function.Surjective (qc : B →ₐ[ZMod p] Bc) := hqc
  let eK : (B ⧸ K) ≃ₐ[ZMod p] Bc := Ideal.quotientKerAlgEquivOfSurjective hqc'
  let ubar : B ⧸ K →ₐ[ZMod p] B ⧸ K := Ideal.quotientMapₐ K (u : B →ₐ[ZMod p] B) hKu
  let ucA : Bc →ₐ[ZMod p] Bc := (eK : (B ⧸ K) →ₐ[ZMod p] Bc).comp (ubar.comp (eK.symm : Bc →ₐ[ZMod p] (B ⧸ K)))
  have heK : ∀ b : B, eK (Ideal.Quotient.mk K b) = qc b := fun b => by
    rw [Ideal.quotientKerAlgEquivOfSurjective_apply]; rfl
  have hucA : ∀ b : B, ucA (qc b) = qc (u b) := by
    intro b
    show eK (ubar (eK.symm (qc b))) = qc (u b)
    have h1 : eK.symm (qc b) = Ideal.Quotient.mk K b := by
      rw [← heK, AlgEquiv.symm_apply_apply]
    rw [h1]
    show eK (Ideal.Quotient.mk K (u b)) = qc (u b)
    exact heK (u b)
  have hucA' : ucA.comp (qc : B →ₐ[ZMod p] Bc) = (qc : B →ₐ[ZMod p] Bc).comp (u : B →ₐ[ZMod p] B) := by
    apply AlgHom.ext; intro b; exact hucA b

  have hqc_comul : ∀ b : B, Coalgebra.comul (R := ZMod p) (qc b) =
      Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (qc : B →ₐ[ZMod p] Bc) (Coalgebra.comul (R := ZMod p) b) := by
    intro b
    have := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom qc) b
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply] at this
    exact this.symm
  have hu_comul : ∀ b : B, Coalgebra.comul (R := ZMod p) (u b) =
      Algebra.TensorProduct.map (u : B →ₐ[ZMod p] B) (u : B →ₐ[ZMod p] B) (Coalgebra.comul (R := ZMod p) b) := by
    intro b
    have := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom u) b
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply] at this
    exact this.symm
  have hcounit : (Bialgebra.counitAlgHom (ZMod p) Bc).comp ucA = Bialgebra.counitAlgHom (ZMod p) Bc := by
    apply AlgHom.ext; intro y
    obtain ⟨b, rfl⟩ := hqc y
    show Coalgebra.counit (ucA (qc b)) = Coalgebra.counit (qc b)
    rw [hucA, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  have hcomul : (Algebra.TensorProduct.map ucA ucA).comp (Bialgebra.comulAlgHom (ZMod p) Bc) =
      (Bialgebra.comulAlgHom (ZMod p) Bc).comp ucA := by
    apply AlgHom.ext; intro y
    obtain ⟨b, rfl⟩ := hqc y
    show Algebra.TensorProduct.map ucA ucA (Coalgebra.comul (R := ZMod p) (qc b)) =
      Coalgebra.comul (R := ZMod p) (ucA (qc b))
    rw [hucA, hqc_comul, hqc_comul, hu_comul, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hucA',
      Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
  let uc : Bc →ₐc[ZMod p] Bc := BialgHom.ofAlgHom ucA hcounit hcomul
  have huc : ∀ y : Bc, uc y = ucA y := fun _ => rfl
  refine ⟨uc, ue, ?_, h2', h3', ?_⟩
  · apply BialgHom.ext; intro b
    show qc (u b) = uc (qc b)
    rw [huc, hucA]
  · intro b
    have hucqc : (uc : Bc →ₐ[ZMod p] Bc).comp (qc : B →ₐ[ZMod p] Bc) = (qc : B →ₐ[ZMod p] Bc).comp (u : B →ₐ[ZMod p] B) := by
      apply AlgHom.ext; intro b; exact hucA b
    have hueπe : (ue : Be →ₐ[ZMod p] Be).comp (πe : B →ₐ[ZMod p] Be) = (πe : B →ₐ[ZMod p] Be).comp (u : B →ₐ[ZMod p] B) := by
      apply AlgHom.ext; intro b; exact (h2 b).symm
    rw [hΘ, hΘ, hu_comul, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← hucqc, ← hueπe,
      Algebra.TensorProduct.map_comp, AlgHom.comp_apply]

end S_HopfAlgebra_exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_comp_eq_of_bijective_tensorProduct_comul_zmodp (solution)

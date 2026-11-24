-- Prove2me | solution 1 for GlobalTheory.nonempty_basis_of_basis_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:00.418989+00:00
-- url     : https://prove2.me/submissions/4c5819f1-1079-40ca-a800-3500bfb377c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct Module
namespace GlobalTheory
open TensorProduct Module in
variable {B A M : Type*} [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A]
  [AddCommGroup M] [Module B M] {r : ℕ} in
private lemma finrank_fiber_eq (hinj : Function.Injective (algebraMap B A))
    (b : Basis (Fin r) A (A ⊗[B] M)) (P : Ideal B) [P.IsMaximal] :
    letI := Ideal.Quotient.field P
    finrank (B ⧸ P) ((B ⧸ P) ⊗[B] M) = r := by
  letI := Ideal.Quotient.field P
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  letI := Ideal.Quotient.field Q
  have h1 : finrank (A ⧸ Q) ((A ⧸ Q) ⊗[A] (A ⊗[B] M)) = r := by
    rw [finrank_eq_card_basis (Algebra.TensorProduct.basis (A ⧸ Q) b), Fintype.card_fin]
  rw [← Module.finrank_baseChange (R := A ⧸ Q),
    (AlgebraTensorModule.cancelBaseChange B (B ⧸ P) (A ⧸ Q) (A ⧸ Q) M).finrank_eq,
    ← (AlgebraTensorModule.cancelBaseChange B A (A ⧸ Q) (A ⧸ Q) M).finrank_eq, h1]
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory
open TensorProduct Module
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {B A M : Type*} [CommRing B] [CommRing A]
    [Finite (MaximalSpectrum B)] [Algebra B A] [Algebra.IsIntegral B A] [AddCommGroup M]
    [Module B M] [Module.Finite B M] {r : ℕ}
    (hinj : Function.Injective (algebraMap B A)) (b : Basis (Fin r) A (A ⊗[B] M)) :
    Nonempty (Basis (Fin r) B M) := by
  classical
  haveI := Fintype.ofFinite (MaximalSpectrum B)
  have hfib : ∀ P : MaximalSpectrum B, ∃ e : Fin r → M,
      Submodule.span (B ⧸ P.asIdeal) (Set.range fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = ⊤ := by
    intro P
    haveI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    let β := Module.finBasisOfFinrankEq (B ⧸ P.asIdeal) _ (finrank_fiber_eq hinj b P.asIdeal)
    choose e he using fun j => TensorProduct.mk_surjective B M (B ⧸ P.asIdeal)
      Ideal.Quotient.mk_surjective (β j)
    refine ⟨e, ?_⟩
    have : (fun j => (1 : B ⧸ P.asIdeal) ⊗ₜ[B] e j) = β := funext he
    rw [this, β.span_eq]
  choose e he using hfib
  have hcrt : ∀ P : MaximalSpectrum B, ∃ c : B,
      ∀ P' : MaximalSpectrum B, c - (if P' = P then 1 else 0) ∈ P'.asIdeal := fun P =>
    Ideal.exists_forall_sub_mem_ideal (I := fun P' : MaximalSpectrum B => P'.asIdeal)
      (fun P₁ P₂ h => by
        haveI := P₁.isMaximal
        haveI := P₂.isMaximal
        exact Ideal.isCoprime_of_isMaximal fun h' => h (MaximalSpectrum.ext h')) _
  choose c hc using hcrt
  let x : Fin r → M := fun j => ∑ P, c P • e P j
  let N := Submodule.span B (Set.range x)
  have key : ∀ P : MaximalSpectrum B, (⊤ : Submodule B (M ⧸ N)) ≤ P.asIdeal • ⊤ := by
    intro P
    have hmk : ∀ P', Ideal.Quotient.mk P.asIdeal (c P') = if P = P' then 1 else 0 := by
      intro P'
      have := hc P' P
      split_ifs at this ⊢ with h
      · rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
        exact this
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using this)
    have hsm : ∀ (a : B) (y : (B ⧸ P.asIdeal) ⊗[B] M),
        a • y = Ideal.Quotient.mk P.asIdeal a • y := fun a y =>
      (algebraMap_smul (B ⧸ P.asIdeal) a y).symm
    have hx : ∀ j, (1 : B ⧸ P.asIdeal) ⊗ₜ[B] x j = 1 ⊗ₜ e P j := by
      intro j
      simp only [x, tmul_sum, tmul_smul]
      simp only [hsm, hmk, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    have h0 : N.mkQ.baseChange (B ⧸ P.asIdeal) = 0 := by
      apply LinearMap.ext_on_range (he P)
      intro j
      rw [← hx, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨j, rfl⟩), tmul_zero,
        LinearMap.zero_apply]
    have hsurj : Function.Surjective (N.mkQ.baseChange (B ⧸ P.asIdeal)) :=
      LinearMap.lTensor_surjective (B ⧸ P.asIdeal) N.mkQ_surjective
    have hsub : Subsingleton ((B ⧸ P.asIdeal) ⊗[B] (M ⧸ N)) := ⟨fun y z => by
      obtain ⟨y', rfl⟩ := hsurj y
      obtain ⟨z', rfl⟩ := hsurj z
      simp [h0]⟩
    have hq := (TensorProduct.quotTensorEquivQuotSMul (M ⧸ N) P.asIdeal).symm.toEquiv.subsingleton
    rw [Submodule.Quotient.subsingleton_iff] at hq
    rw [hq]
  have hann : Module.annihilator B (M ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht1, ht⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul P ⊤
      Module.Finite.fg_top (key ⟨P, hP⟩)
    have htP : t ∈ P := hle (Module.mem_annihilator.mpr fun q => ht q trivial)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.sub_mem htP ht1))
  have hN : N = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have h1 : (1 : B) ∈ Module.annihilator B (M ⧸ N) := hann ▸ Submodule.mem_top
    have := Module.mem_annihilator.mp h1 (N.mkQ m)
    simpa [Submodule.Quotient.mk_eq_zero] using this
  let f := Fintype.linearCombination B x
  have hfs : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hN
  let F := f.baseChange A
  have hFs : Function.Surjective F := LinearMap.lTensor_surjective A hfs
  let φ : (Fin r → A) →ₗ[A] (Fin r → A) := b.equivFun.toLinearMap ∘ₗ F ∘ₗ
    (TensorProduct.piScalarRight B A A (Fin r)).symm.toLinearMap
  have hφs : Function.Surjective φ := by
    simpa [φ] using b.equivFun.surjective.comp
      (hFs.comp (TensorProduct.piScalarRight B A A (Fin r)).symm.surjective)
  have hφi := OrzechProperty.injective_of_surjective_endomorphism φ hφs
  have hFi : Function.Injective F := by
    intro y z hyz
    have := @hφi (TensorProduct.piScalarRight B A A (Fin r) y)
      (TensorProduct.piScalarRight B A A (Fin r) z) (by
        simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hyz])
    exact (TensorProduct.piScalarRight B A A (Fin r)).injective this
  have hfi : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : F ((1 : A) ⊗ₜ v) = F 0 := by
      rw [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, tmul_zero, map_zero]
    have h2 := congrArg (TensorProduct.piScalarRight B A A (Fin r)) (hFi h1)
    rw [Submodule.mem_bot]
    funext i
    exact hinj (by rw [Pi.zero_apply, map_zero, Algebra.algebraMap_eq_smul_one]; simpa using congrFun h2 i)
  exact ⟨Basis.ofEquivFun (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm⟩
end _root_.GlobalTheory
end GlobalTheory

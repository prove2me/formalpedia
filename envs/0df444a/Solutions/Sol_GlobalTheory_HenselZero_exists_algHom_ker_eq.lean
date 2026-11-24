-- Prove2me | solution 1 for GlobalTheory.HenselZero.exists_algHom_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:23:27.0807+00:00
-- url     : https://prove2.me/submissions/f0310199-7984-42cb-913c-100bfcfe7007

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Theorems.Thm_GlobalTheory_HenselZero_formallySmooth_quotient
import Theorems.Thm_GlobalTheory_HenselZero_exists_derivation_lift
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
open IsLocalRing GlobalTheory.SqZero
namespace GlobalTheory.HenselZero
theorem _root_.solution {O S ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [Algebra.FormallySmooth O S] [Fintype ι] [DecidableEq ι] (f : ι → S) (u : S →+* ResidueField O)
    (hu : ∀ r, u (algebraMap O S r) = residue O r) (hf : ∀ i, u (f i) = 0)
    (χ : ι → (S →+* DualNumber (ResidueField O))) (h₁ : ∀ k a, (χ k a).fst = u a)
    (h₂ : ∀ k r, χ k (algebraMap O S r) = algebraMap (ResidueField O) _ (residue O r))
    (hd : (Matrix.of fun i k => (χ k (f i)).snd).det ≠ 0)
    (hm : maximalIdeal S ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map (algebraMap O S)) :
    ∃ ψ : S →ₐ[O] O, (∀ a, residue O (ψ a) = u a) ∧ RingHom.ker ψ = Ideal.span (Set.range f) := by
  let u' : S →ₐ[O] ResidueField O := ⟨u, hu⟩
  have hs : Function.Surjective u' := fun c => by
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨_, hu r⟩
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective u hs)
  have hτ : ∀ k, ∃ τ : Derivation O S S, ∀ a, u (τ a) = (χ k a).snd := fun k =>
    exists_derivation_lift u' hs
      { toFun := fun a => (χ k a).snd
        map_add' := fun a b => by simp
        map_smul' := fun r a => by
          rw [Algebra.smul_def, map_mul, h₂, Algebra.smul_def]
          simp [TrivSqZeroExt.algebraMap_eq_inl] }
      fun a b => by simp [h₁, mul_comm]; rfl
  choose τ hτ using hτ
  have hunit : IsUnit (Matrix.of fun i k => τ k (f i)).det := by
    rw [← notMem_maximalIdeal, ← hker, RingHom.mem_ker, RingHom.map_det]
    refine fun h => hd (Eq.trans ?_ h)
    congr 1
    ext i k
    exact (hτ k _).symm
  have := formallySmooth_quotient f τ hunit
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker u' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal O)
    (Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) u' fun a ha => hle ha)
  let ψ : S →ₐ[O] O := g.comp (Ideal.Quotient.mkₐ O _)
  have hψ : ∀ a, residue O (ψ a) = u a := fun a => congr($hg (Ideal.Quotient.mk _ a))
  have hle' : Ideal.span (Set.range f) ≤ RingHom.ker ψ := fun a ha => by
    show g (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  refine ⟨ψ, hψ, le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S)
    (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_) hle'⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have ha₀ : ψ a = 0 := ha
  have ha' : a ∈ maximalIdeal S := by rw [← hker, RingHom.mem_ker, ← hψ, ha₀, map_zero]
  replace ha' := hm ha'
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at ha'
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hc
  refine Submodule.add_mem_sup hb (Submodule.smul_mem_smul (r := algebraMap O S π) (n := c) ?_ ?_)
  · rw [← hker, RingHom.mem_ker, hu, residue_eq_zero_iff]
    exact hπ.not_isUnit
  · have hb₀ : ψ b = 0 := hle' hb
    rw [map_add, hb₀, zero_add, map_mul, AlgHom.commutes] at ha₀
    exact (mul_eq_zero.1 ha₀).resolve_left hπ.ne_zero
end GlobalTheory.HenselZero

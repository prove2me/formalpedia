-- Prove2me | solution 1 for GlobalTheory.many_independent_products_in_function_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:54:57.146233+00:00
-- url     : https://prove2.me/submissions/a534b733-46fd-44bb-ae8f-275a9579921d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecializationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionField
import Theorems.Thm_GlobalTheory_prod_mem_span_range_prod_mul
import Theorems.Thm_GlobalTheory_T_adjoinRoot_complex_map_linearIndependent
import Theorems.Thm_GlobalTheory_T_exists_formal_branches_of_separable_reduction
import Theorems.Thm_GlobalTheory_T_finrank_mul_pow_le_finrank_of_prod_mem
import Theorems.Thm_P2M_GlobalTheory_T_exists_primitive_monic_separable_specialization__83c1351e5fd3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ)
    (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K),
    LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K,
    LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧
      v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by
  intro K _ _ D x hx J _ e he m hm
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hxQ : IsTranscendenceBasis ℚ x := (Algebra.IsAlgebraic.isTranscendenceBasis_iff ℤ ℚ).1 hx
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 he
  obtain ⟨P, ψ, g, c, hPm, hψ, hψx, hg, hge, hsep⟩ := GlobalTheory.T.exists_primitive_monic_separable_specialization' K D x hxQ J e
  choose e' he' using fun j => (AlgHom.mem_range ψ).1 (hge j)
  have he'Q : LinearIndependent ℚ e' := by
    have h1 : LinearIndependent ℚ (fun j => g * e j) := by
      refine heQ.map' (LinearMap.mulLeft ℚ g) (LinearMap.ker_eq_bot.2 ?_)
      exact mul_right_injective₀ hg
    have h2 : (ψ.toLinearMap ∘ e') = fun j => g * e j := funext he'
    exact LinearIndependent.of_comp ψ.toLinearMap (h2 ▸ h1)
  obtain ⟨τ, hτX, hτq, hτind⟩ := GlobalTheory.T.adjoinRoot_complex_map_linearIndependent D P hPm
  have hPCm : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).Monic := hPm.map _
  have hsepC : ((P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map
      (MvPolynomial.eval (fun i => (c i : ℂ)))).Separable := by
    have h : (P.map (MvPolynomial.map (algebraMap ℚ ℂ))).map (MvPolynomial.eval (fun i => (c i : ℂ))) =
        (P.map (MvPolynomial.eval c)).map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext <;> simp
    rw [h]; exact hsep.map
  let PC := P.map (MvPolynomial.map (algebraMap ℚ ℂ))
  obtain ⟨n, φ, hφinj, hφX⟩ := GlobalTheory.T.exists_formal_branches_of_separable_reduction D PC (fun i => (c i : ℂ)) hPCm hsepC
  let w : (Fin m → J) × (Fin D → Fin m) → AdjoinRoot P := fun ub =>
    (∏ l, e' (ub.1 l)) * ∏ i, AdjoinRoot.of P (MvPolynomial.X i) ^ (ub.2 i : ℕ)
  obtain ⟨κ, a, ha, hspan, hind⟩ := exists_linearIndependent' ℚ w
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let xC : Fin D → AdjoinRoot PC := fun i => AdjoinRoot.of PC (MvPolynomial.X i)
  let F : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun j => τ (e' j))
  let G : Submodule ℂ (AdjoinRoot PC) := Submodule.span ℂ (Set.range fun k => τ (w (a k)))
  haveI : Module.Finite ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  haveI : Module.Finite ℂ G := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hτspan : ∀ u ∈ Submodule.span ℚ (Set.range (w ∘ a)), τ u ∈ G := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact G.add_mem hy hz
    | smul q y _ hy => rw [hτq]; exact G.smul_mem _ hy
  have key := GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem D n (AdjoinRoot PC) φ xC (fun i => (c i : ℂ)) hφinj hφX F G m hm (by
    intro f b hf hb
    have h1 := prod_mem_span_range_prod_mul (R := ℂ) (fun j => τ (e' j)) m f hf (∏ i, xC i ^ b i)
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨u, rfl⟩
    have hw : w (u, fun i => ⟨b i, hb i⟩) ∈ Submodule.span ℚ (Set.range (w ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    have h2 := hτspan _ hw
    simpa [w, map_prod, map_mul, map_pow, hτX, xC] using h2)
  have hFr : Module.finrank ℂ F = Fintype.card J := finrank_span_eq_card (hτind J e' he'Q)
  have hGr : Module.finrank ℂ G ≤ Fintype.card κ := finrank_range_le_card _
  let L : AdjoinRoot P →ₗ[ℚ] K := (LinearMap.mulLeft ℚ ((g ^ m)⁻¹)).comp ψ.toLinearMap
  have hL : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot.2 ?_
    show Function.Injective (fun u => (g ^ m)⁻¹ * ψ u)
    exact (mul_right_injective₀ (inv_ne_zero (pow_ne_zero _ hg))).comp hψ
  have hindK : LinearIndependent ℚ (L ∘ (w ∘ a)) := hind.map' L hL
  have hcard : Fintype.card J * m ^ D ≤ Fintype.card κ := hFr ▸ (key.trans hGr)
  let emb : Fin (Fintype.card J * m ^ D) ↪ κ :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin κ).symm.toEmbedding
  refine ⟨L ∘ (w ∘ a) ∘ emb, ?_, ?_⟩
  · exact (hindK.comp emb emb.injective).restrict_scalars' ℤ
  · intro s
    refine ⟨(a (emb s)).1, fun i => ((a (emb s)).2 i : ℕ), fun i => ((a (emb s)).2 i).isLt, ?_⟩
    simp only [Function.comp_apply, L, w, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.mulLeft_apply, map_mul, map_prod, map_pow, hψx, he', Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
end GlobalTheory

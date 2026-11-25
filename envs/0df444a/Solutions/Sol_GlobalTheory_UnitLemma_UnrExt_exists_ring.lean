-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.exists_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:12:41.598819+00:00
-- url     : https://prove2.me/submissions/defd874d-4608-473c-af8f-cc03b0b77c62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_exists_root
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_root_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_complete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_dvr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_exists_monic_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isLocal


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
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.UnitLemma.UnrExt
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    {q f d : ℕ} (hq : Nat.card (ResidueField O) = q ^ 2) (hf : q = p ^ f) (hd : Odd d) (c : O →+* O)
    (hcc : ∀ x, c (c x) = x) (hc : ∀ x, residue O (c x) = residue O x ^ q) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (_ : Finite (ResidueField W)) (_ : Algebra O W) (c' : W →+* W) (z : W),
      Module.Finite O W ∧ Function.Injective (algebraMap O W) ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O W ϖ)) ∧ Module.finrank O W = d ∧
      Nat.card (ResidueField W) = (q ^ d) ^ 2 ∧ (∀ y, c' (c' y) = y) ∧
      (∀ x, c' (algebraMap O W x) = algebraMap O W (c x)) ∧ z - c' z ∉ maximalIdeal W ∧
      IsPrimitiveRoot z ((q ^ d) ^ 2 - 1) ∧ Algebra.adjoin O {z} = ⊤ := by
  haveI : NeZero d := ⟨hd.pos.ne'⟩
  let k := ResidueField O
  let k' := FiniteField.Extension k p d
  have hrk : Module.finrank k k' = d := FiniteField.finrank_extension k p d
  have hcard : Nat.card k' = (q ^ d) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := k), hrk, hq, ← pow_mul, ← pow_mul, mul_comm]
  haveI : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hq2 : 2 ≤ q ^ d := by
    have h1 : 1 < Nat.card k' := Finite.one_lt_card
    rw [hcard] at h1
    by_contra h
    have : q ^ d = 0 ∨ q ^ d = 1 := by omega
    rcases this with h | h <;> simp [h] at h1
  set N := (q ^ d) ^ 2 - 1 with hN
  have hNpos : q ^ d - 1 < N := by
    have : q ^ d < (q ^ d) ^ 2 := by nlinarith
    omega
  obtain ⟨αu, hαu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := k'ˣ)
  rw [Nat.card_units, hcard, ← hN] at hαu
  let α : k' := αu
  have hα : IsPrimitiveRoot α N := by
    rw [← hαu]; exact IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.orderOf αu)
  have hpowk' : ∀ y : k', y ^ ((q ^ d) ^ 2) = y := fun y => by
    haveI := Fintype.ofFinite k'
    rw [← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hgen : ∀ y : k', y ≠ 0 → ∃ i, α ^ i = y := fun y hy => by
    haveI : NeZero N := ⟨by omega⟩
    have : y ^ N = 1 := by
      apply mul_left_cancel₀ hy
      rw [← pow_succ', mul_one, show N + 1 = (q ^ d) ^ 2 by omega, hpowk']
    obtain ⟨i, -, hi⟩ := hα.eq_pow_of_pow_eq_one this
    exact ⟨i, hi⟩
  have hint : IsIntegral k α := .of_finite k α
  have htop : IntermediateField.adjoin k {α} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]; exact zero_mem _
    · obtain ⟨i, rfl⟩ := hgen y hy
      exact pow_mem (IntermediateField.mem_adjoin_simple_self k α) i
  have hdeg : (minpoly k α).natDegree = d := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hrk]
  obtain ⟨g, hgm, hgd, hg⟩ := Nb.exists_monic_lift (minpoly k α) (minpoly.monic hint)
  have hirr : Irreducible (g.map (residue O)) := hgm ▸ minpoly.irreducible hint
  haveI := Nb.isDomain g hg hirr
  haveI := Nb.isLocal g hg hirr
  haveI := Nb.dvr g hg hirr
  haveI := Nb.complete g hg hirr
  haveI := Nb.finite g hg
  let W := AdjoinRoot g
  let u : O →+* k' := (algebraMap k k').comp (residue O)
  have hgu : g.map u = (minpoly k α).map (algebraMap k k') := by rw [← hgm, Polynomial.map_map]
  have hsep : (g.map u).Separable := by
    rw [hgu]; exact Separable.map (Algebra.IsSeparable.isSeparable k α)
  have hev : g.eval₂ u α = 0 := by
    rw [← eval_map, hgu, eval_map]; exact minpoly.aeval k α
  let v : W →+* k' := AdjoinRoot.lift u α hev
  have hvr : v (AdjoinRoot.root g) = α := AdjoinRoot.lift_root hev
  have hva : v.comp (AdjoinRoot.of g) = u := by
    exact RingHom.ext fun x => AdjoinRoot.lift_of hev
  have hmax : maximalIdeal W = (maximalIdeal O).map (algebraMap O W) := Nb.maxEq g hg hirr
  have hker : RingHom.ker v = maximalIdeal W := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply, hva]
      simp only [u, RingHom.comp_apply]
      rw [(residue_eq_zero_iff x).2 hx, map_zero]
  have hsurj : Function.Surjective v := fun y => by
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    · obtain ⟨i, rfl⟩ := hgen y hy
      exact ⟨AdjoinRoot.root g ^ i, by rw [map_pow, hvr]⟩
  let e : ResidueField W ≃+* k' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  let τ : k' →+* k' := iterateFrobenius k' p (f * d)
  have hτ : ∀ y, τ y = y ^ (q ^ d) := fun y => by
    rw [hf, ← pow_mul]; exact iterateFrobenius_def ..
  have hττ : ∀ y, τ (τ y) = y := fun y => by
    rw [hτ, hτ, ← pow_mul, ← sq, hpowk']
  have hτu : τ.comp u = u.comp c := by
    ext x
    have h1 : ∀ (y : k) (m : ℕ), y ^ (q ^ (2 * m + 1)) = y ^ q := fun y m => by
      haveI := Fintype.ofFinite k
      rw [pow_succ, pow_mul, pow_mul, ← hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]
    obtain ⟨m, hm⟩ := hd
    simp only [u, RingHom.comp_apply]
    rw [hτ, hc, ← map_pow, show q ^ d = q ^ (2 * m + 1) from congrArg _ hm, h1]
  have hG : (g.map ((AdjoinRoot.of g).comp c)).map v = (g.map u).map τ := by
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hva, hτu]
  obtain ⟨w, hw, hvw⟩ := exists_root v hker hsurj (g.map ((AdjoinRoot.of g).comp c)) (hg.map _)
    (by rw [hG]; exact hsep.map) (τ α) (by rw [hG, eval_map, eval₂_at_apply, eval_map, hev, map_zero])
  rw [eval_map] at hw
  let c' : W →+* W := AdjoinRoot.lift _ w hw
  have hc'r : c' (AdjoinRoot.root g) = w := AdjoinRoot.lift_root hw
  have hc'a : c'.comp (AdjoinRoot.of g) = (AdjoinRoot.of g).comp c := by
    exact RingHom.ext fun x => AdjoinRoot.lift_of hw
  have hvc : v.comp c' = τ.comp v := by
    apply AdjoinRoot.ringHom_ext
    · rw [RingHom.comp_assoc, hc'a, ← RingHom.comp_assoc, hva, ← hτu, RingHom.comp_assoc _ v τ, hva]
    · simp only [RingHom.comp_apply]
      rw [hc'r, hvw, hvr]
  have hvc' : ∀ y, v (c' y) = τ (v y) := fun y => RingHom.congr_fun hvc y
  have hcca : (c'.comp c').comp (AdjoinRoot.of g) = AdjoinRoot.of g := by
    rw [RingHom.comp_assoc, hc'a, ← RingHom.comp_assoc, hc'a]
    ext x; simp [hcc]
  have hinv : c'.comp c' = RingHom.id W := by
    apply AdjoinRoot.ringHom_ext
    · rw [hcca]; rfl
    · refine root_unique v hker (g.map (AdjoinRoot.of g)) (by rw [Polynomial.map_map, hva]; exact hsep) ?_ ?_ ?_
      · have h1 := hom_eval₂ g (AdjoinRoot.of g) (c'.comp c') (AdjoinRoot.root g)
        rw [AdjoinRoot.eval₂_root, map_zero, hcca] at h1
        rw [eval_map]; exact h1.symm
      · rw [eval_map]; exact AdjoinRoot.eval₂_root g
      · exact (hvc' _).trans ((congrArg τ (hvc' _)).trans (hττ _))
  have hNk : (N : k') ≠ 0 := by
    haveI := Fintype.ofFinite k'
    have h1 : ((N + 1 : ℕ) : k') = 0 := by
      rw [show N + 1 = (q ^ d) ^ 2 by omega, ← hcard, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h1
  obtain ⟨z, hz, hvz⟩ := exists_root v hker hsurj (X ^ N - 1) (by simpa using monic_X_pow_sub_C (1 : W) (by omega : N ≠ 0))
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) α (by simp [hα.pow_eq_one])
  have hz1 : z ^ N = 1 := by simpa [sub_eq_zero] using hz
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, Finite.of_equiv _ e.symm.toEquiv,
    inferInstance, c', z, inferInstance, Nb.inj g hg hirr, fun ϖ hϖ => ?_, ?_, ?_, fun y => RingHom.congr_fun hinv y,
    fun x => RingHom.congr_fun hc'a x, ?_, ⟨hz1, fun l hl => hα.dvd_of_pow_eq_one l ?_⟩, ?_⟩
  · rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, hmax, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  · rw [(AdjoinRoot.powerBasis' hg).finrank, AdjoinRoot.powerBasis'_dim, hgd, hdeg]
  · rw [Nat.card_congr e.toEquiv, hcard]
  · rw [← hker, RingHom.mem_ker, map_sub, hvc', hvz, hτ, sub_eq_zero]
    intro h
    have h1 : α ^ (q ^ d - 1) = 1 := by
      apply mul_left_cancel₀ αu.ne_zero
      rw [← pow_succ', mul_one, show q ^ d - 1 + 1 = q ^ d by omega]
      exact h.symm
    have := Nat.le_of_dvd (by omega) (hα.dvd_of_pow_eq_one _ h1)
    omega
  · rw [← hvz, ← map_pow, hl, map_one]
  · have key : (⊤ : Submodule O W) ≤ Subalgebra.toSubmodule (Algebra.adjoin O {z}) := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top
        (maximalIdeal_le_jacobson _) fun y _ => ?_
      have hm : ∀ t : W, v t = 0 → t ∈ (maximalIdeal O • ⊤ : Submodule O W) := fun t ht => by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hmax, ← hker]
        exact ht
      by_cases hy : v y = 0
      · exact Submodule.mem_sup_right (hm y hy)
      · obtain ⟨i, hi⟩ := hgen _ hy
        rw [show y = z ^ i + (y - z ^ i) by ring]
        exact Submodule.add_mem_sup (pow_mem (Algebra.self_mem_adjoin_singleton O z) i)
          (hm _ (by rw [map_sub, map_pow, hvz, hi, sub_self]))
    rw [eq_top_iff]
    exact fun y _ => key Submodule.mem_top
end GlobalTheory.UnitLemma.UnrExt

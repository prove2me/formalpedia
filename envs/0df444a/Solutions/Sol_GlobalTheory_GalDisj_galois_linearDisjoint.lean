-- Prove2me | solution 1 for GlobalTheory.GalDisj.galois_linearDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:16.21346+00:00
-- url     : https://prove2.me/submissions/16d51c5a-b4d7-41e5-96de-62fa2ebaa542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace GlobalTheory.GalDisj
section
variable {k M F D : Type*} [Field k] [Field M] [Field F] [Field D] [Algebra k M] [Algebra k F]
  [Algebra k D] [Algebra M D] [Algebra F D] [IsScalarTower k M D] [IsScalarTower k F D]
end
open Polynomial in
private theorem natDegree_minpoly_le_natDegree_minpoly_map {k Ω D : Type} [Field k] [Field Ω] [Field D]
    [Algebra k Ω] (o : Ω →+* D) (F : Subfield D)
    (hF : ∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) (α : Ω) (hα : IsIntegral k α)
    (hsplit : ((minpoly k α).map (algebraMap k Ω)).Splits) :
    (minpoly k α).natDegree ≤ (minpoly F (o α)).natDegree := by
  set ψ : k →+* F := (o.comp (algebraMap k Ω)).codRestrict F (fun c => (hF _).2 ⟨c, rfl⟩)
  have hcomp : F.subtype.comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hcomp' : (algebraMap F D).comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hmon : ((minpoly k α).map ψ).Monic := (minpoly.monic hα).map ψ
  have hroot : aeval (o α) ((minpoly k α).map ψ) = 0 := by
    rw [aeval_def, eval₂_map, hcomp', ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hβ : IsIntegral F (o α) := ⟨_, hmon, hroot⟩
  have hdvd : minpoly F (o α) ∣ (minpoly k α).map ψ := minpoly.dvd F _ hroot
  have hP : ((minpoly k α).map ψ).map F.subtype = ((minpoly k α).map (algebraMap k Ω)).map o := by
    rw [map_map, map_map, hcomp]
  have hP0 : ((minpoly k α).map ψ).map F.subtype ≠ 0 := (hmon.map _).ne_zero
  have hGdvd : (minpoly F (o α)).map F.subtype ∣ ((minpoly k α).map ψ).map F.subtype :=
    Polynomial.map_dvd _ hdvd
  have hGs : ((minpoly F (o α)).map F.subtype).Splits := by
    refine Splits.of_dvd ?_ hP0 hGdvd
    rw [hP]
    exact hsplit.map o
  have hGm : ((minpoly F (o α)).map F.subtype).Monic := (minpoly.monic hβ).map _
  have hlift : (minpoly F (o α)).map F.subtype ∈ lifts o := by
    refine hGs.mem_lift_of_roots_mem_range hGm o fun a ha => ?_
    have h1 := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hP0 hGdvd) ha
    rw [hP, hsplit.roots_map o] at h1
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h1
    exact ⟨r, rfl⟩
  have hlift' : (minpoly F (o α)).map F.subtype ∈ lifts (o.comp (algebraMap k Ω)) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨y, hy⟩ := hlift n
    have hyF : o y ∈ F := by
      rw [hy, coeff_map]
      exact ((minpoly F (o α)).coeff n).2
    obtain ⟨c, rfl⟩ := (hF y).1 hyF
    exact ⟨c, hy⟩
  obtain ⟨g, hg⟩ := (mem_lifts _).1 hlift'
  have hinj : Function.Injective (o.comp (algebraMap k Ω)) := RingHom.injective _
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hg
    exact hGm.ne_zero hg.symm
  have hgα : aeval α g = 0 := by
    apply o.injective
    rw [map_zero, aeval_def, hom_eval₂, ← eval_map, hg, eval_map]
    exact minpoly.aeval F (o α)
  calc (minpoly k α).natDegree ≤ g.natDegree := natDegree_le_of_dvd (minpoly.dvd k α hgα) hg0
    _ = ((minpoly F (o α)).map F.subtype).natDegree := by
        rw [← hg, natDegree_map_eq_of_injective hinj]
    _ = (minpoly F (o α)).natDegree := natDegree_map_eq_of_injective (RingHom.injective _) _
end GlobalTheory.GalDisj
end

set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.GalDisj
open Polynomial
namespace GlobalTheory.GalDisj
namespace _root_.GlobalTheory.GalDisj
theorem _root_.solution : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  intro k Ω D _ _ _ _ _ o F hF m x hx b hb hsum
  classical
  set M := IntermediateField.adjoin k (Set.range x)
  haveI : FiniteDimensional k M :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  obtain ⟨α', hα'⟩ := Field.exists_primitive_element k M
  set α : Ω := (α' : Ω) with hαdef
  have hxα : ∀ i, x i ∈ IntermediateField.adjoin k {α} := by
    intro i
    have h1 : (IntermediateField.adjoin k {α'}).map M.val = IntermediateField.adjoin k {α} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [← h1, hα']
    exact ⟨⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩, trivial, rfl⟩
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim ≤ (minpoly F (o α)).natDegree := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    exact natDegree_minpoly_le_natDegree_minpoly_map o F hF α hint (IsGalois.splits k α)
  have hli : LinearIndependent F (fun j : Fin pb.dim => o α ^ (j : ℕ)) :=
    (linearIndependent_pow (o α)).comp (Fin.castLE hdim) (Fin.castLE_injective hdim)
  set c : Fin m → Fin pb.dim → k := fun i j => pb.basis.repr ⟨x i, hxα i⟩ j
  have hexp : ∀ i, x i = ∑ j, c i j • α ^ (j : ℕ) := by
    intro i
    have h := congrArg Subtype.val (pb.basis.sum_repr ⟨x i, hxα i⟩)
    refine h.symm.trans ?_
    simp [c, pb, IntermediateField.adjoin.powerBasis_gen]
  have hd : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i = 0 := by
    have hmem : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i ∈ F := fun j =>
      F.sum_mem fun i _ => F.mul_mem ((hF _).2 ⟨_, rfl⟩) (hb i)
    intro j
    have := Fintype.linearIndependent_iff.1 hli (fun j => ⟨_, hmem j⟩) ?_ j
    · exact congrArg Subtype.val this
    rw [← hsum]
    simp only [hexp, Subfield.smul_def, map_sum, map_smul, Algebra.smul_def, map_mul, map_pow,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (∑ i, o (algebraMap k Ω (c i j)) * b i) * o α ^ (j : ℕ) = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hx.repr
  have hgx : ∀ i, g (x i) = Finsupp.single i 1 := by
    intro i
    have := LinearMap.congr_fun hg ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hx.repr_eq_single i _ rfl]
  intro l
  calc b l = ∑ i, o (algebraMap k Ω (g (x i) l)) * b i := by
        simp [hgx, Finsupp.single_apply]
    _ = ∑ j : Fin pb.dim, o (algebraMap k Ω (g (α ^ (j : ℕ)) l)) *
          ∑ i, o (algebraMap k Ω (c i j)) * b i := by
        simp only [hexp, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by simp [hd]
end _root_.GlobalTheory.GalDisj
end GlobalTheory.GalDisj

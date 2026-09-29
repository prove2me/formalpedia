-- Prove2me | solution 1 for IntermediateField.isSolvable_algEquiv_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a6cabb21-22ab-5c5d-b391-b6bb04981bf3

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Theorems.Thm_Subgroup_exists_wild_tame_cyclic_unramified_chain_of_le
import Theorems.Thm_IntermediateField_exists_le_adjoin_padicEmbedding_image
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_tame_generator_at_level
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_isSolvable_algEquiv_of_padic
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"

set_option autoImplicit false
open ExtCitation
open scoped IntermediateField Pointwise

private theorem mul_comm_of_forall_eq_pow {Q : Type*} [Group Q] (g : Q) (h : ∀ x : Q, ∃ n : ℕ, x = g ^ n)
    (a b : Q) : a * b = b * a := by
  obtain ⟨m, rfl⟩ := h a
  obtain ⟨n, rfl⟩ := h b
  exact Commute.pow_pow_self g m n

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E] [Normal K E] :
    Group.IsSolvable (E ≃ₐ[K] E) := by
  classical

  obtain ⟨qq, hqq⟩ : ∃ qq : Nat.Primes, (qq : ℕ) = q := ⟨⟨q, Fact.out⟩, rfl⟩
  subst hqq
  haveI : IsGalois ℚ_[qq] (PadicAlgCl qq) := IsAlgClosure.isGalois ℚ_[qq] (PadicAlgCl qq)

  let S : Subgroup (primeLocalGaloisGroup qq) := (K.fixingSubgroup : Subgroup (PadicAlgCl qq ≃ₐ[ℚ_[qq]] PadicAlgCl qq))
  haveI : FiniteDimensional ℚ_[qq] (E.restrictScalars ℚ_[qq]) := FiniteDimensional.trans ℚ_[qq] K E
  let H : Subgroup (primeLocalGaloisGroup qq) :=
    ((E.restrictScalars ℚ_[qq]).fixingSubgroup : Subgroup (PadicAlgCl qq ≃ₐ[ℚ_[qq]] PadicAlgCl qq))
  have hSmem : ∀ g : PadicAlgCl qq ≃ₐ[ℚ_[qq]] PadicAlgCl qq, g ∈ S ↔ ∀ x : PadicAlgCl qq, x ∈ K → g x = x :=
    fun g => IntermediateField.mem_fixingSubgroup_iff K g
  have hHmem : ∀ g : PadicAlgCl qq ≃ₐ[ℚ_[qq]] PadicAlgCl qq, g ∈ H ↔ ∀ x : PadicAlgCl qq, x ∈ E → g x = x := by
    intro g
    rw [show (g ∈ H ↔ g ∈ (E.restrictScalars ℚ_[qq]).fixingSubgroup) from Iff.rfl, IntermediateField.mem_fixingSubgroup_iff]
    exact forall_congr' fun x => by rw [IntermediateField.mem_restrictScalars]
  have hKE : ∀ x : PadicAlgCl qq, x ∈ K → x ∈ E := fun x hx => E.algebraMap_mem ⟨x, hx⟩
  have hHS : H ≤ S := fun g hg => (hSmem g).2 fun x hx => (hHmem g).1 hg x (hKE x hx)
  let ψ : S →* (E ≃ₐ[K] E) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := PadicAlgCl qq) E).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  have hψsurj : Function.Surjective ψ :=
    (AlgEquiv.restrictNormalHom_surjective (PadicAlgCl qq)).comp (IntermediateField.fixingSubgroupEquiv K).surjective
  have hHker : H.subgroupOf S = ψ.ker := by
    ext s
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hs
      rw [show ψ s = AlgEquiv.restrictNormalHom E (IntermediateField.fixingSubgroupEquiv K s) from rfl,
        ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (hHmem _).1 hs x hx
    · intro hψ
      have h' : IntermediateField.fixingSubgroupEquiv K s ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := PadicAlgCl qq) E).ker := hψ
      rw [IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff] at h'
      exact (hHmem _).2 h'
  have hHn : (H.subgroupOf S).Normal := by rw [hHker]; infer_instance

  suffices hsolv : Group.IsSolvable (S ⧸ H.subgroupOf S) by
    haveI := hsolv
    refine solvable_of_surjective (f := QuotientGroup.lift (H.subgroupOf S) ψ hHker.le) fun y => ?_
    obtain ⟨s, rfl⟩ := hψsurj y
    exact ⟨QuotientGroup.mk s, rfl⟩

  obtain ⟨φ, hφ⟩ := exists_isFrobeniusAt_apply_primeLocalToGlobal qq
  obtain ⟨F₀, hF₀fd, hEF₀⟩ := IntermediateField.exists_le_adjoin_padicEmbedding_image (qq : ℕ) (E.restrictScalars ℚ_[qq])
  haveI := hF₀fd
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F₀ (AlgebraicClosure ℚ)
  haveI hFfd : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ F₀ _
  haveI hFgal : IsGalois ℚ F := by
    haveI : Normal ℚ F := normalClosure.normal ℚ F₀ _
    exact ⟨⟩
  have hF₀F : F₀ ≤ F := IntermediateField.le_normalClosure F₀
  let U : Subgroup (primeLocalGaloisGroup qq) := (F.fixingSubgroup).comap (primeLocalToGlobal qq)
  haveI hUn : U.Normal := by
    haveI : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).mpr hFgal
    exact Subgroup.Normal.comap inferInstance _
  let Kw : IntermediateField ℚ_[qq] (PadicAlgCl qq) :=
    IntermediateField.adjoin ℚ_[qq] (padicEmbedding qq '' (F : Set (AlgebraicClosure ℚ)))
  haveI : FiniteDimensional ℚ_[qq] Kw := IntermediateField.finiteDimensional_adjoin_padicEmbedding_image qq F
  have hUK : U = (Kw.fixingSubgroup : Subgroup (PadicAlgCl qq ≃ₐ[ℚ_[qq]] PadicAlgCl qq)) := by
    ext s; exact localGaloisToGlobal_mem_fixingSubgroup_iff qq F s
  haveI hUfi : U.FiniteIndex := by
    refine ⟨?_⟩
    rw [hUK]
    show (Kw.fixingSubgroup : Subgroup (PadicAlgCl qq ≃ₐ[ℚ_[qq]] PadicAlgCl qq)).index ≠ 0
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  have hUH : U ≤ H := by
    rw [hUK]
    have hle : E.restrictScalars ℚ_[qq] ≤ Kw := hEF₀.trans
      (IntermediateField.adjoin.mono _ _ _ (Set.image_mono (fun x hx => hF₀F hx)))
    exact IntermediateField.fixingSubgroup_antitone hle

  obtain ⟨t, W, -, hUW, -, hWn, hWq, hIt, hφt⟩ := exists_tame_generator_at_level qq φ hφ F
  haveI := hWn
  have hgen : ∀ g : primeLocalGaloisGroup qq, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ Subgroup.closure {t} ⊔ W := by
    intro g
    obtain ⟨n, hn⟩ := exists_frobenius_pow_inv_mul_mem_inertia_sup_level qq φ hφ F g
    refine ⟨n, ?_⟩
    refine (sup_le (fun i hi => ?_) (hUW.trans le_sup_right)) hn
    obtain ⟨a, ha⟩ := hIt i hi
    have hmem : t ^ a * ((t ^ a)⁻¹ * i) ∈ Subgroup.closure {t} ⊔ W :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_singleton t)) a))
        (Subgroup.mem_sup_right ha)
    rwa [mul_inv_cancel_left] at hmem
  obtain ⟨P, I, hHP, hPI, hIS, hPn, hIn, ⟨n, hPH⟩, -, ⟨g₁, hg₁I, hcycI⟩, ⟨g₀, hg₀S, hcycS⟩⟩ :=
    Subgroup.exists_wild_tame_cyclic_unramified_chain_of_le U W hUW hWq t φ hφt hgen S H hUH hHS hHn

  haveI := hHn; haveI := hPn; haveI := hIn
  haveI : (H.subgroupOf S).FiniteIndex := by
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hUH
    infer_instance
  haveI : Finite (S ⧸ H.subgroupOf S) := Subgroup.finite_quotient_of_finiteIndex
  let mk : S →* S ⧸ H.subgroupOf S := QuotientGroup.mk' _
  have hmk : ∀ s : S, mk s = 1 ↔ (s : primeLocalGaloisGroup qq) ∈ H := fun s => QuotientGroup.eq_one_iff s
  let Ib : Subgroup (S ⧸ H.subgroupOf S) := (I.subgroupOf S).map mk
  let Pb : Subgroup (S ⧸ H.subgroupOf S) := (P.subgroupOf S).map mk
  haveI hIbN : Ib.Normal := Subgroup.Normal.map hIn _ (QuotientGroup.mk'_surjective _)
  haveI hPbN : Pb.Normal := Subgroup.Normal.map hPn _ (QuotientGroup.mk'_surjective _)
  have hPbIb : Pb ≤ Ib := Subgroup.map_mono fun s hs => hPI hs

  have hQI : Group.IsSolvable ((S ⧸ H.subgroupOf S) ⧸ Ib) := by
    apply Group.isSolvable_of_comm
    apply mul_comm_of_forall_eq_pow (QuotientGroup.mk (mk ⟨g₀, hg₀S⟩))
    intro x
    induction x using QuotientGroup.induction_on with
    | H y =>
      induction y using QuotientGroup.induction_on with
      | H s =>
        obtain ⟨m, hm⟩ := hcycS s s.2
        refine ⟨m, ?_⟩
        rw [← QuotientGroup.mk_pow, ← map_pow, eq_comm, QuotientGroup.eq]
        exact Subgroup.mem_map.mpr ⟨(⟨g₀, hg₀S⟩ ^ m)⁻¹ * s, Subgroup.mem_subgroupOf.mpr (by simpa using hm), by
          rw [map_mul, map_inv]; rfl⟩

  have hPb : Group.IsSolvable Pb := by
    have hPG : IsPGroup (qq : ℕ) Pb := by
      rintro ⟨x, hx⟩
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      haveI : (H.subgroupOf P).Normal := by
        have : (H.subgroupOf P) = ((H.subgroupOf S).comap (Subgroup.inclusion (hPI.trans hIS))) := by
          ext y; simp [Subgroup.mem_subgroupOf]
        rw [this]; exact Subgroup.Normal.comap hHn _
      have hpow : (⟨(s : primeLocalGaloisGroup qq), hs⟩ : P) ^ ((qq : ℕ) ^ n) ∈ H.subgroupOf P := by
        rw [← hPH]; exact Subgroup.pow_index_mem _ _
      rw [Subgroup.mem_subgroupOf] at hpow
      change ((s : primeLocalGaloisGroup qq)) ^ ((qq : ℕ) ^ n) ∈ H at hpow
      refine ⟨n, Subtype.ext ?_⟩
      show (mk s) ^ ((qq : ℕ) ^ n) = 1
      rw [← map_pow, hmk]
      exact hpow
    haveI : Fact (qq : ℕ).Prime := inferInstance
    haveI := hPG.isNilpotent
    infer_instance

  have hIb : Group.IsSolvable Ib := by
    haveI : (Pb.subgroupOf Ib).Normal := inferInstance
    haveI : Group.IsSolvable (Pb.subgroupOf Ib) := by
      haveI := hPb
      exact solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hPbIb).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPbIb).symm.surjective
    haveI : Group.IsSolvable (Ib ⧸ Pb.subgroupOf Ib) := by
      apply Group.isSolvable_of_comm
      obtain ⟨hg₁S⟩ : PLift (g₁ ∈ S) := ⟨hIS hg₁I⟩
      apply mul_comm_of_forall_eq_pow
        (QuotientGroup.mk (⟨mk ⟨g₁, hg₁S⟩, Subgroup.mem_map.mpr ⟨⟨g₁, hg₁S⟩, Subgroup.mem_subgroupOf.mpr hg₁I, rfl⟩⟩ : Ib))
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨s, hs, hys⟩ := Subgroup.mem_map.mp y.2
        rw [Subgroup.mem_subgroupOf] at hs
        obtain ⟨m, hm⟩ := hcycI s hs
        refine ⟨m, ?_⟩
        rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        refine Subgroup.mem_map.mpr ⟨(⟨g₁, hg₁S⟩ ^ m)⁻¹ * s, Subgroup.mem_subgroupOf.mpr (by simpa using hm), ?_⟩
        simp only [map_mul, map_inv, map_pow, hys, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact solvable_of_ker_le_range (Pb.subgroupOf Ib).subtype (QuotientGroup.mk' (Pb.subgroupOf Ib))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

  haveI := hIb
  haveI := hQI
  exact solvable_of_ker_le_range Ib.subtype (QuotientGroup.mk' Ib) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end S_IntermediateField_isSolvable_algEquiv_of_padic
end P2MW
export P2MW.S_IntermediateField_isSolvable_algEquiv_of_padic (solution)

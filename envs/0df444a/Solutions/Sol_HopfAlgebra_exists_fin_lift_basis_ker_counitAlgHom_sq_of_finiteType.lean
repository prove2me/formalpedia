-- Prove2me | solution 1 for HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4aa4c47c-4443-5965-8fd0-bc326a61546f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType

open Bialgebra Coalgebra

set_option maxHeartbeats 4800000

noncomputable section

theorem solution
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (ξ : Fin n → A),
      (∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ∧
      LinearIndependent K
        (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)) ∧
      (∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
        ∃ c : Fin n → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) := by
  classical
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI

  have haugProj_mem : ∀ a : A, a - algebraMap K A (Coalgebra.counit (R := K) a) ∈ I := by
    intro a
    show Coalgebra.counit (R := K) (a - algebraMap K A (Coalgebra.counit (R := K) a)) = 0
    have hε1 : Coalgebra.counit (R := K) (algebraMap K A (Coalgebra.counit (R := K) a))
        = Coalgebra.counit (R := K) a := (Bialgebra.counitAlgHom K A).commutes _
    rw [map_sub, hε1, sub_self]

  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  let Q := Ideal.Quotient.mk (I ^ 2)

  have hspanA : ∀ a ∈ I, Q a ∈ Submodule.span K (Q '' (↑s : Set A)) := by
    intro a ha
    have ha' : a ∈ Submodule.span A (↑s : Set A) := hs ▸ ha
    rw [Finsupp.mem_span_iff_linearCombination] at ha'
    obtain ⟨r, rfl⟩ := ha'
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hsmul : (r j • (↑j : A)) = r j * ↑j := rfl
    have hdecomp : r j * (↑j : A)
        = algebraMap K A (Coalgebra.counit (R := K) (r j)) * (↑j : A)
          + (r j - algebraMap K A (Coalgebra.counit (R := K) (r j))) * (↑j : A) := by ring
    have hjI : (↑j : A) ∈ I := hs ▸ Ideal.subset_span j.2
    have hI2 : (r j - algebraMap K A (Coalgebra.counit (R := K) (r j))) * (↑j : A) ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (haugProj_mem (r j)) hjI
    rw [hsmul, hdecomp, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hI2, add_zero, map_mul]
    rw [show Q (algebraMap K A (Coalgebra.counit (R := K) (r j)))
        = algebraMap K (A ⧸ I^2) (Coalgebra.counit (R := K) (r j)) from rfl,
      ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨↑j, j.2, rfl⟩)

  let V : Submodule K (A ⧸ I ^ 2) := Submodule.span K (Q '' (↑s : Set A))
  haveI : Module.Finite K V := Module.Finite.span_of_finite K (s.finite_toSet.image _)
  let B := Module.Free.chooseBasis K V
  haveI : Fintype (Module.Free.ChooseBasisIndex K V) := inferInstance

  have hVsub : ∀ v ∈ V, ∃ a ∈ I, Q a = v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g, hg, rfl⟩; exact ⟨g, hs ▸ Ideal.subset_span hg, rfl⟩
    · exact ⟨0, I.zero_mem, map_zero Q⟩
    · rintro x y _ _ ⟨a, haI, rfl⟩ ⟨b, hbI, rfl⟩
      exact ⟨a + b, I.add_mem haI hbI, map_add Q a b⟩
    · rintro c x _ ⟨a, haI, rfl⟩
      refine ⟨c • a, ?_, map_smul (Ideal.Quotient.mkₐ K (I^2)) c a⟩
      rw [Algebra.smul_def]; exact I.mul_mem_left _ haI
  choose ξ' hξ'I hξ'Q using fun j => hVsub (B j).1 (B j).2

  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex K V)).symm
  let n := Fintype.card (Module.Free.ChooseBasisIndex K V)
  refine ⟨n, fun i => ξ' (e i), fun i => hξ'I (e i), ?_, ?_⟩
  ·
    have hBli' : LinearIndependent K (fun j => ((B j : V) : A ⧸ I^2)) :=
      B.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    have hQξ' : (fun j => Q (ξ' j)) = (fun j => ((B j : V) : A ⧸ I^2)) := funext hξ'Q
    have : LinearIndependent K (fun j => Q (ξ' j)) := hQξ' ▸ hBli'
    exact this.comp e e.injective
  ·
    intro a haI
    have haV : Q a ∈ V := hspanA a haI
    set v : V := ⟨Q a, haV⟩
    refine ⟨fun i => B.repr v (e i), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hsubv : V.subtype v = ∑ j, B.repr v j • (B j : A ⧸ I^2) := by
      conv_lhs => rw [← B.sum_repr v]
      simp only [map_sum, map_smul, Submodule.coe_subtype]
    have hsumeq : Q a = ∑ i : Fin n, B.repr v (e i) • Q (ξ' (e i)) := by
      rw [show Q a = V.subtype v from rfl, hsubv, ← e.sum_comp]
      exact Finset.sum_congr rfl fun j _ => by rw [hξ'Q (e j)]
    rw [hsumeq]
    refine sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ => ?_)
    exact (map_smul (Ideal.Quotient.mkₐ K (I^2)) (B.repr v (e i)) (ξ' (e i))).symm

end

end S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
end P2MW
export P2MW.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType (solution)

-- Prove2me | solution 1 for GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:40.815745+00:00
-- url     : https://prove2.me/submissions/e9738ea5-5958-4d2b-9315-d745c17b52f6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
import Theorems.Thm_GroundTheory_Arith_Jacobian_ker_le_maximalIdeal
import Theorems.Thm_GroundTheory_Arith_Jacobian_spanFinrank_quotient_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Jacobian
open IsLocalRing TensorProduct
universe u
noncomputable section
variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]
variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))
variable [IsNoetherianRing P]
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S]
include hsurj
namespace GroundTheory.Arith.Jacobian
theorem _root_.solution {κ : Type} [Fintype κ] (f : κ → P)
    (hfI : ∀ i, f i ∈ RingHom.ker (algebraMap P S))
    (hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2)
    (d : ℕ) (hμ : (maximalIdeal S).spanFinrank ≤ d) (hdim : (d : WithBot ℕ∞) ≤ ringKrullDim S) :
    RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) := by
  set J := Ideal.span (Set.range f)
  have hJI : J ≤ RingHom.ker (algebraMap P S) := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hfI i)
  have hJtop : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal P).ne_top (hJI.trans (ker_le_maximalIdeal hsurj))
  have : Nontrivial (P ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have : IsLocalRing (P ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let ψ : P ⧸ J →+* S := Ideal.Quotient.lift J (algebraMap P S) (fun x hx => hJI hx)
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨x, rfl⟩ := hsurj s
    exact ⟨Ideal.Quotient.mk J x, rfl⟩
  have hspan := spanFinrank_quotient_le hsurj J hcov
  have h1 : ringKrullDim S ≤ ringKrullDim (P ⧸ J) := ringKrullDim_le_of_surjective ψ hψ
  have h2 : ringKrullDim (P ⧸ J) ≤ (maximalIdeal (P ⧸ J)).spanFinrank :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  have h3 : ((maximalIdeal (P ⧸ J)).spanFinrank : WithBot ℕ∞) ≤ d := by
    exact_mod_cast hspan.trans hμ
  have : IsRegularLocalRing (P ⧸ J) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (h3.trans (hdim.trans h1))
  have : IsDomain (P ⧸ J) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hz0
    have h5 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hz0)
    let ψ' : (P ⧸ J) ⧸ Ideal.span {z} →+* S := Ideal.Quotient.lift (Ideal.span {z}) ψ (by
      intro w hw
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hw
      rw [map_mul, hz, mul_zero])
    have hψ' : Function.Surjective ψ' := by
      intro s
      obtain ⟨w, hw⟩ := hψ s
      exact ⟨Ideal.Quotient.mk _ w, hw⟩
    have h6 := ringKrullDim_le_of_surjective ψ' hψ'
    have h7 : (d : WithBot ℕ∞) + 1 ≤ d :=
      calc (d : WithBot ℕ∞) + 1 ≤ ringKrullDim S + 1 := by gcongr
        _ ≤ ringKrullDim ((P ⧸ J) ⧸ Ideal.span {z}) + 1 := by gcongr
        _ ≤ ringKrullDim (P ⧸ J) := h5
        _ ≤ d := h2.trans h3
    have h8 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : ℕ) := by exact_mod_cast h7
    have h9 : d + 1 ≤ d := by exact_mod_cast h8
    omega
  intro x hx
  have hx' : ψ (Ideal.Quotient.mk J x) = 0 := RingHom.mem_ker.1 hx
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hinj (hx'.trans (map_zero ψ).symm))
end GroundTheory.Arith.Jacobian

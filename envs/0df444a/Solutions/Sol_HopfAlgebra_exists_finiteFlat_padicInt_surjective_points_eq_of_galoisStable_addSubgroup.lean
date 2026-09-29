-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cae65ec1-f8c7-5406-b83d-59b67e6155fb

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped PadicInt TensorProduct
open WithConv

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk exists_quotientFlag_of_galoisStableChain_of_fixedPoints"
namespace LocalClosure
p2m_open "HopfAlgebra"

section FinitePoints

variable {R : Type} [CommRing R] {G : Type} [CommRing G] [HopfAlgebra R G]
  {L : Type} [Field L] [Algebra R L]

noncomputable def iR (R G L : Type) [CommRing R] [CommRing G] [HopfAlgebra R G] [Field L] [Algebra R L] :
    WithConv (G →ₐ[R] L ⊗[R] G) := toConv Algebra.TensorProduct.includeRight

noncomputable def ptExt (φ : WithConv (G →ₐ[R] L)) : L ⊗[R] G →ₐ[L] L :=
  Algebra.TensorProduct.lift (Algebra.ofId L L) φ.ofConv fun _ _ => .all _ _

lemma ptExt_comp_iR (φ : WithConv (G →ₐ[R] L)) :
    ((ptExt φ).restrictScalars R).comp (iR R G L).ofConv = φ.ofConv :=
  Algebra.TensorProduct.lift_comp_includeRight _ _ _

lemma algHom_eq_of_ker_eq {A : Type} [CommRing A] [Algebra L A] {χ χ' : A →ₐ[L] L}
    (h : RingHom.ker χ = RingHom.ker χ') : χ = χ' := by
  apply AlgHom.ext
  intro x
  have hx : x - algebraMap L A (χ x) ∈ RingHom.ker χ' := by
    rw [← h, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at hx
  exact hx.symm

theorem finite_points [Module.Finite R G] : Finite (WithConv (G →ₐ[R] L)) := by
  haveI : IsArtinianRing (L ⊗[R] G) := IsArtinianRing.of_finite L (L ⊗[R] G)
  refine Finite.of_injective (fun φ : WithConv (G →ₐ[R] L) =>
    (⟨RingHom.ker (ptExt φ), RingHom.ker_isPrime _⟩ : PrimeSpectrum (L ⊗[R] G))) ?_
  intro φ φ' h
  have h' : ptExt φ = ptExt φ' := algHom_eq_of_ker_eq (congrArg PrimeSpectrum.asIdeal h)
  apply WithConv.ext
  rw [← ptExt_comp_iR φ, ← ptExt_comp_iR φ', h']

end FinitePoints

theorem padicAlgCl_fixed (p : ℕ) [Fact p.Prime] (c : PadicAlgCl p)
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ c = c) :
    c ∈ Set.range (algebraMap ℚ_[p] (PadicAlgCl p)) := by
  haveI : Algebra.IsAlgebraic ℚ_[p] (PadicAlgCl p) := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal ℚ_[p] (PadicAlgCl p)
  haveI : Algebra.IsSeparable ℚ_[p] (PadicAlgCl p) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois ℚ_[p] (PadicAlgCl p) := IsGalois.mk
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed c).mpr hc

theorem main
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    (N : AddSubgroup M) (hN : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M), m ∈ N → σ • m ∈ N) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ (ϖ : G →ₐc[ℤ_[p]] H), Function.Surjective ϖ ∧
        (∀ h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) ∈ N) ∧
        (∀ m ∈ N, ∃! h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) = m) ∧
        (∀ h h' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv (h * h')).comp (ϖ : G →ₐ[ℤ_[p]] H))) =
            e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) +
              e (WithConv.toConv ((WithConv.ofConv h').comp (ϖ : G →ₐ[ℤ_[p]] H)))) := by
  classical
  haveI : Finite (WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)) := finite_points
  haveI : Finite M := Finite.of_equiv _ e

  have hR : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

  have hfix : ∀ c : PadicAlgCl p, (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      (∀ r : ℤ_[p], σ (algebraMap ℤ_[p] (PadicAlgCl p) r) = algebraMap ℤ_[p] (PadicAlgCl p) r) → σ c = c) →
      ∃ a b : ℤ_[p], algebraMap ℤ_[p] (PadicAlgCl p) b ≠ 0 ∧
        c * algebraMap ℤ_[p] (PadicAlgCl p) b = algebraMap ℤ_[p] (PadicAlgCl p) a := by
    intro c hc
    have hc' : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ c = c := fun σ => hc σ (fun r => by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), AlgEquiv.commutes])
    obtain ⟨x, hx⟩ := padicAlgCl_fixed p c hc'
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) x
    have hb0 : (algebraMap ℤ_[p] ℚ_[p] b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨a, b, ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
      exact (map_ne_zero _).mpr hb0
    · rw [← hx, ← hab, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p) b,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p) a, ← map_mul,
        div_mul_cancel₀ _ hb0]

  let Nc : Fin (1 + 1) → AddSubgroup M := ![N, ⊤]
  have hmono : ∀ i : Fin 1, Nc i.castSucc ≤ Nc i.succ := by
    intro i
    fin_cases i
    exact le_top
  have htop : Nc (Fin.last 1) = ⊤ := rfl
  have hstab : ∀ (i : Fin (1 + 1)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : M),
      x ∈ Nc i → (fun (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M) => σ • m) σ x ∈ Nc i := by
    intro i σ x hx
    fin_cases i
    · exact hN σ x hx
    · exact AddSubgroup.mem_top _
  obtain ⟨B, _instB, _instH, π, φ, hft, hflat, hπsurj, hφsurj, hcomp, hbij, hfactor, hcocomm, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints (K := ℚ_[p]) (L := PadicAlgCl p)
      ℤ_[p] hR hfix G M e he_add (fun σ m => σ • m) he_act 1 Nc hmono htop hstab
  have hN0 : Nc 0 = N := rfl
  refine ⟨B 0, inferInstance, inferInstance, (hfin inferInstance 0).1, hflat 0, hcocomm inferInstance 0,
    π 0, hπsurj 0, ?_, ?_, ?_⟩
  ·
    intro h
    have := (hfactor 0 ((ofConv h).comp (π 0 : G →ₐ[ℤ_[p]] B 0))).mp ⟨ofConv h, rfl⟩
    rwa [hN0] at this
  ·
    intro m hm
    have hfac : ∃ g : B 0 →ₐ[ℤ_[p]] PadicAlgCl p, g.comp (π 0 : G →ₐ[ℤ_[p]] B 0) = ofConv (e.symm m) := by
      rw [hfactor 0, toConv_ofConv, Equiv.apply_symm_apply, hN0]
      exact hm
    obtain ⟨g, hg⟩ := hfac
    refine ⟨toConv g, ?_, ?_⟩
    · show e (toConv ((ofConv (toConv g)).comp (π 0 : G →ₐ[ℤ_[p]] B 0))) = m
      rw [ofConv_toConv, hg, toConv_ofConv, Equiv.apply_symm_apply]
    · intro h' hh'
      apply WithConv.ext
      show ofConv h' = ofConv (toConv g)
      rw [ofConv_toConv]
      have h1 : (ofConv h').comp (π 0 : G →ₐ[ℤ_[p]] B 0) = g.comp (π 0 : G →ₐ[ℤ_[p]] B 0) := by
        rw [hg]
        apply WithConv.toConv_injective
        apply e.injective
        rw [hh', toConv_ofConv, Equiv.apply_symm_apply]
      apply AlgHom.ext
      intro y
      obtain ⟨x, rfl⟩ := hπsurj 0 y
      exact congrArg (fun (ψ : G →ₐ[ℤ_[p]] PadicAlgCl p) => ψ x) h1
  ·
    intro h h'
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv, he_add]

end HopfAlgebra.LocalClosure

theorem solution
    (p : ℕ) [Fact p.Prime]
    (G : Type) [CommRing G] [HopfAlgebra ℤ_[p] G] [Module.Finite ℤ_[p] G] [Module.Flat ℤ_[p] G]
    [Coalgebra.IsCocomm ℤ_[p] G]
    {M : Type} [AddCommGroup M] [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (G →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    (N : AddSubgroup M) (hN : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M), m ∈ N → σ • m ∈ N) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ (ϖ : G →ₐc[ℤ_[p]] H), Function.Surjective ϖ ∧
        (∀ h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) ∈ N) ∧
        (∀ m ∈ N, ∃! h : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) = m) ∧
        (∀ h h' : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv (h * h')).comp (ϖ : G →ₐ[ℤ_[p]] H))) =
            e (WithConv.toConv ((WithConv.ofConv h).comp (ϖ : G →ₐ[ℤ_[p]] H))) +
              e (WithConv.toConv ((WithConv.ofConv h').comp (ϖ : G →ₐ[ℤ_[p]] H)))) :=
  HopfAlgebra.LocalClosure.main p G e he_add he_act N hN

end S_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_padicInt_surjective_points_eq_of_galoisStable_addSubgroup (solution)

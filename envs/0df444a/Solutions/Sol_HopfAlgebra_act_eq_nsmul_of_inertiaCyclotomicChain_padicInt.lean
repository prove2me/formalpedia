-- Prove2me | solution 1 for HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/68655e57-d853-5ad4-bb0e-68ef2dfe221b

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt
import Theorems.Thm_CartierDual_exists_equiv_algHom_padicAlgCl_monoidHom_units
import Theorems.Thm_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_act_eq_nsmul_of_inertiaCyclotomicChain_padicInt
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

namespace S17CycloChain

open scoped PadicInt

variable (p : ℕ) [Fact p.Prime]

noncomputable def gal {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p)) :
    WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p) :=
  WithConv.toConv (((σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toAlgHom.restrictScalars ℤ_[p]).comp
    (WithConv.ofConv f))

variable {p}

theorem gal_apply {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p)) (a : A) :
    gal p σ f a = σ (f a) := rfl

theorem pt_ext {A : Type} [CommRing A] [Algebra ℤ_[p] A] (f g : WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p))
    (hfg : ∀ a, f a = g a) : f = g := by
  rw [← WithConv.toConv_ofConv f, ← WithConv.toConv_ofConv g]
  exact congrArg WithConv.toConv (AlgHom.ext hfg)

theorem gal_mul {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p)) :
    gal p σ (gal p τ f) = gal p (σ * τ) f := pt_ext _ _ (fun _ => rfl)

theorem gal_one {A : Type} [CommRing A] [Algebra ℤ_[p] A] (f : WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p)) :
    gal p 1 f = f := pt_ext _ _ (fun _ => rfl)

theorem gal_inv {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : WithConv (A →ₐ[ℤ_[p]] PadicAlgCl p)) :
    gal p σ (gal p σ⁻¹ f) = f := by rw [gal_mul, mul_inv_cancel, gal_one]

variable (p) in

theorem exists_cycloExp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ m : ℕ, ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ m := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsCyclic ↥(rootsOfUnity p (PadicAlgCl p)) := rootsOfUnity.isCyclic (PadicAlgCl p) p
  let φ : ↥(rootsOfUnity p (PadicAlgCl p)) →* ↥(rootsOfUnity p (PadicAlgCl p)) :=
    restrictRootsOfUnity (σ : PadicAlgCl p →+* PadicAlgCl p) p
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ
  have hq0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨(m % p).toNat, fun ζ hζ => ?_⟩
  let z : ↥(rootsOfUnity p (PadicAlgCl p)) := rootsOfUnity.mkOfPowEq ζ hζ
  have hz : ((z : (PadicAlgCl p)ˣ) : PadicAlgCl p) = ζ := rootsOfUnity.coe_mkOfPowEq hζ
  have hzq : z ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity p (z : (PadicAlgCl p)ˣ)).mp z.2
  have h1 : σ ζ = ((φ z : ↥(rootsOfUnity p (PadicAlgCl p))) : (PadicAlgCl p)ˣ) := by
    rw [restrictRootsOfUnity_coe_apply, hz]; rfl
  have h2 : φ z = z ^ ((m % p).toNat : ℤ) := by
    rw [hm z, zpow_eq_zpow_emod m hzq, Int.toNat_of_nonneg (Int.emod_nonneg _ hq0.ne')]
  rw [h1, h2, zpow_natCast, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, hz]

theorem pow_exp_inv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (c' : ℕ)
    (hc' : ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ⁻¹ ζ = ζ ^ c') (u : PadicAlgCl p) (hu : u ^ p = 1) :
    (σ u) ^ c' = u := by
  have hσu : (σ u) ^ p = 1 := by rw [← map_pow, hu, map_one]
  rw [← hc' _ hσu, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

end S17CycloChain

open S17CycloChain in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0)
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → M → M)
    (hact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (n : ℕ) (N : Fin (n + 1) → AddSubgroup M)
    (hbot : N 0 = ⊥) (htop : N (Fin.last n) = ⊤) (hmono : ∀ i : Fin n, N i.castSucc ≤ N i.succ)
    (hstab : ∀ (i : Fin (n + 1)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : M),
      x ∈ N i → act σ x ∈ N i)
    (hstep : ∀ i : Fin n,
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
          ∀ x ∈ N i.succ, act σ x - c • x ∈ N i.castSucc) :
    ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ c : ℕ, (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        ∀ x : M, act σ x = c • x := by
  classical
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing

  have he1 : e 1 = 0 := by
    have h := he 1 1
    rw [mul_one] at h
    have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have he_pow : ∀ (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) (m : ℕ), e (f ^ m) = m • e f := by
    intro f m
    induction m with
    | zero => rw [pow_zero, zero_smul, he1]
    | succ m ih => rw [pow_succ, he, ih, succ_nsmul]
  have hact_e : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      act σ (e f) = e (gal p σ f) := fun σ f => (hact σ f (gal p σ f) (fun h => rfl)).symm
  have hfp : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1 := by
    intro f
    apply e.injective
    rw [he_pow, hM, he1]

  obtain ⟨d, hd_mul, hd_gal⟩ := CartierDual.exists_equiv_algHom_padicAlgCl_monoidHom_units p H
  have hd_gal' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (φ : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p)) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      ((d (gal p σ φ) (gal p σ f) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = σ ((d φ f : (PadicAlgCl p)ˣ) : PadicAlgCl p) :=
    fun σ φ f => hd_gal σ φ (gal p σ φ) (fun y => rfl) f (gal p σ f) (fun x => rfl)
  have hd_rootOfUnity : ∀ (φ : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p))
      (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)), ((d φ f : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ p = 1 := by
    intro φ f
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hfp, map_one, Units.val_one]

  let X : Type := WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ
  let e' : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ Additive X := d.trans Additive.ofMul
  have he'_apply : ∀ φ, Additive.toMul (e' φ) = d φ := fun _ => rfl
  have he' : ∀ φ ψ, e' (φ * ψ) = e' φ + e' ψ := by
    intro φ ψ
    apply Additive.toMul.injective
    rw [he'_apply, hd_mul, toMul_add, he'_apply, he'_apply]
  let act' : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Additive X → Additive X :=
    fun σ y => e' (gal p σ (e'.symm y))
  have hact'_e : ∀ σ φ, act' σ (e' φ) = e' (gal p σ φ) := by
    intro σ φ
    show e' (gal p σ (e'.symm (e' φ))) = e' (gal p σ φ)
    rw [Equiv.symm_apply_apply]
  have hact' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (φ φ' : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ y : CartierDual ℤ_[p] H, φ' y = σ (φ y)) → e' φ' = act' σ (e' φ) := by
    intro σ φ φ' hφ
    have : φ' = gal p σ φ := pt_ext _ _ (fun y => hφ y)
    rw [this, hact'_e]

  let Ann : AddSubgroup M → AddSubgroup (Additive X) := fun S =>
    { carrier := {y | ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), e f ∈ S → Additive.toMul y f = 1}
      zero_mem' := fun f _ => by rw [toMul_zero, MonoidHom.one_apply]
      add_mem' := fun {a b} ha hb f hf => by rw [toMul_add, MonoidHom.mul_apply, ha f hf, hb f hf, mul_one]
      neg_mem' := fun {a} ha f hf => by rw [toMul_neg, MonoidHom.inv_apply, ha f hf, inv_one] }
  have mem_Ann : ∀ (S : AddSubgroup M) (y : Additive X),
      y ∈ Ann S ↔ ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), e f ∈ S → Additive.toMul y f = 1 :=
    fun _ _ => Iff.rfl
  let N' : Fin (n + 1) → AddSubgroup (Additive X) := fun j => Ann (N (Fin.rev j))
  have hbot' : N' 0 = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    have hy' : ∀ f, Additive.toMul y f = 1 := fun f =>
      (mem_Ann _ _).mp hy f (by rw [Fin.rev_zero, htop]; exact AddSubgroup.mem_top _)
    rw [AddSubgroup.mem_bot]
    apply Additive.toMul.injective
    rw [toMul_zero]
    exact MonoidHom.ext hy'
  have htop' : N' (Fin.last n) = ⊤ := by
    apply le_antisymm le_top
    intro y _
    rw [show N' (Fin.last n) = Ann (N (Fin.rev (Fin.last n))) from rfl, mem_Ann]
    intro f hf
    rw [Fin.rev_last, hbot, AddSubgroup.mem_bot] at hf
    have : f = 1 := e.injective (by rw [hf, he1])
    rw [this, map_one]
  have hmono' : ∀ i : Fin n, N' i.castSucc ≤ N' i.succ := by
    intro i y hy
    rw [show N' i.succ = Ann (N (Fin.rev i.succ)) from rfl, mem_Ann]
    intro f hf
    refine (mem_Ann _ _).mp hy f ?_
    rw [Fin.rev_castSucc]
    rw [Fin.rev_succ] at hf
    exact hmono _ hf
  have hstab' : ∀ (j : Fin (n + 1)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : Additive X),
      y ∈ N' j → act' σ y ∈ N' j := by
    intro j σ y hy
    obtain ⟨φ, rfl⟩ := e'.surjective y
    rw [hact'_e]
    rw [show N' j = Ann (N (Fin.rev j)) from rfl, mem_Ann] at hy ⊢
    intro f hf
    apply Units.val_injective
    rw [he'_apply, ← gal_inv σ f, hd_gal', Units.val_one]
    have hmem : e (gal p σ⁻¹ f) ∈ N (Fin.rev j) := by
      rw [← hact_e]; exact hstab _ _ _ hf
    have := hy (gal p σ⁻¹ f) hmem
    rw [he'_apply] at this
    rw [this, Units.val_one, map_one]
  have hstep' : ∀ i : Fin n, ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ y ∈ N' i.succ, act' σ y - y ∈ N' i.castSucc := by
    intro i σ hσ y hy
    obtain ⟨φ, rfl⟩ := e'.surjective y
    rw [hact'_e]
    rw [show N' i.succ = Ann (N (Fin.rev i.succ)) from rfl, mem_Ann, Fin.rev_succ] at hy
    rw [show N' i.castSucc = Ann (N (Fin.rev i.castSucc)) from rfl, mem_Ann, Fin.rev_castSucc]
    intro f hf
    rw [toMul_sub, he'_apply, he'_apply, MonoidHom.div_apply, div_eq_one]

    obtain ⟨c', hc'⟩ := exists_cycloExp p σ⁻¹
    have hσ' : σ⁻¹ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] := inv_mem hσ
    have hdisp : act σ⁻¹ (e f) - c' • e f ∈ N ((Fin.rev i).castSucc) := hstep (Fin.rev i) σ⁻¹ hσ' c' hc' (e f) hf

    set g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := e.symm (act σ⁻¹ (e f) - c' • e f) with hg
    have heg : e g = act σ⁻¹ (e f) - c' • e f := by rw [hg, Equiv.apply_symm_apply]
    have hdecomp : gal p σ⁻¹ f = f ^ c' * g := by
      apply e.injective
      rw [he, he_pow, heg, ← hact_e, add_sub_cancel]
    have hφg : ((d φ g : (PadicAlgCl p)ˣ) : PadicAlgCl p) = 1 := by
      have := hy g (by rw [heg]; exact hdisp)
      rw [he'_apply] at this
      rw [this, Units.val_one]
    apply Units.val_injective
    have hL : ((d (gal p σ φ) f : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        (σ ((d φ f : (PadicAlgCl p)ˣ) : PadicAlgCl p)) ^ c' := by
      conv_lhs => rw [← gal_inv σ f]
      rw [hd_gal', hdecomp, map_mul, Units.val_mul, hφg, mul_one, map_pow, Units.val_pow_eq_pow_val, map_pow]
    rw [hL]
    exact pow_exp_inv σ c' hc' _ (hd_rootOfUnity φ f)

  have hL3 := HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt p hp2 (CartierDual ℤ_[p] H)
    (Additive X) e' he' act' hact' n N' hbot' htop' hmono' hstab' hstep'
  have hfixφ : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ φ : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p), gal p σ φ = φ := by
    intro σ hσ φ
    apply e'.injective
    rw [← hact'_e]
    exact hL3 σ hσ (e' φ)

  have hfinP : Finite (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) := by
    have hcard : Nat.card (H →ₐ[ℤ_[p]] PadicAlgCl p) = Module.finrank ℤ_[p] H :=
      HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ_[p] H (PadicAlgCl p)
    haveI : Nontrivial H := ⟨⟨1, 0, fun h => by
      have := congrArg (Coalgebra.counit (R := ℤ_[p]) (A := H)) h
      rw [Bialgebra.counit_one, map_zero] at this
      exact one_ne_zero this⟩⟩
    have hpos : 0 < Module.finrank ℤ_[p] H := Module.finrank_pos
    haveI : Finite (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpos.ne')
    exact Finite.of_equiv _ (Equiv.ofBijective WithConv.toConv
      ⟨WithConv.toConv_injective, WithConv.toConv_surjective⟩)
  haveI : Finite M := Finite.of_equiv _ e
  have hsep := (MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one p M hM
    (PadicAlgCl p)).1

  let E : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* Multiplicative M :=
    { toFun := fun f => Multiplicative.ofAdd (e f)
      map_one' := by rw [he1, ofAdd_zero]
      map_mul' := fun f g => by rw [he, ofAdd_add] }
  have hE : ∀ f, E f = Multiplicative.ofAdd (e f) := fun _ => rfl

  intro σ hσ c hc x
  obtain ⟨f, rfl⟩ := e.surjective x
  rw [← sub_eq_zero]
  apply hsep
  intro χ
  obtain ⟨φ, hφ⟩ := d.surjective (χ.comp E)
  have hχ : ∀ g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), χ (Multiplicative.ofAdd (e g)) = d φ g := by
    intro g; rw [hφ, MonoidHom.comp_apply, hE]
  rw [ofAdd_sub, map_div, hact_e, ← he_pow, hχ, hχ, div_eq_one]
  apply Units.val_injective
  conv_lhs => rw [← hfixφ σ hσ φ]
  rw [hd_gal', map_pow, Units.val_pow_eq_pow_val]
  exact hc _ (hd_rootOfUnity φ f)

end S_HopfAlgebra_act_eq_nsmul_of_inertiaCyclotomicChain_padicInt
end P2MW
export P2MW.S_HopfAlgebra_act_eq_nsmul_of_inertiaCyclotomicChain_padicInt (solution)

-- Prove2me | solution 1 for HopfAlgebra.act_eq_self_of_inertiaTrivialChain_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/030db11c-e01f-56cd-9099-428b9f9bf872

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_HopfAlgebra_exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt
import Theorems.Thm_HopfAlgebra_mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt
import Theorems.Thm_HopfAlgebra_exists_quotientFlag_of_galoisStableChain_of_fixedPoints
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct NNReal

noncomputable section

namespace S17L3

open WithConv

variable (p : ℕ) [Fact p.Prime]

theorem isGalois_padicAlgCl : IsGalois ℚ_[p] (PadicAlgCl p) := by
  haveI : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal ℚ_[p] (PadicAlgCl p)
  exact IsGalois.mk

theorem algebraMap_padicInt_injective : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem hfix_padicInt (c : PadicAlgCl p)
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      (∀ r : ℤ_[p], σ (algebraMap ℤ_[p] (PadicAlgCl p) r) = algebraMap ℤ_[p] (PadicAlgCl p) r) → σ c = c) :
    ∃ a b : ℤ_[p], algebraMap ℤ_[p] (PadicAlgCl p) b ≠ 0 ∧
      c * algebraMap ℤ_[p] (PadicAlgCl p) b = algebraMap ℤ_[p] (PadicAlgCl p) a := by
  haveI := isGalois_padicAlgCl p
  have hall : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ c = c := fun σ =>
    hc σ (fun r => by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), AlgEquiv.commutes])
  have hmem : c ∈ (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)),
      IntermediateField.mem_fixedField_iff]
    intro σ _
    exact hall σ
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨x, rfl⟩ := hmem
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) x
  have hb0 : algebraMap ℤ_[p] ℚ_[p] b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨a, b, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    exact (map_ne_zero _).mpr hb0
  · rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p) b,
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p) a, ← map_mul, div_mul_cancel₀ _ hb0]

variable (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]

theorem finite_points : Finite (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) := by
  classical
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing
  by_cases hH : Nontrivial H
  · haveI := hH
    have hcard : Nat.card (H →ₐ[ℤ_[p]] PadicAlgCl p) = Module.finrank ℤ_[p] H :=
      HopfAlgebra.natCard_algHom_eq_finrank_of_charZero ℤ_[p] H (PadicAlgCl p)
    haveI : Finite (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
    exact Finite.of_injective WithConv.ofConv WithConv.ofConv_injective
  · rw [not_nontrivial_iff_subsingleton] at hH
    haveI : IsEmpty (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) := ⟨fun f => by
      have h := (WithConv.ofConv f).map_one
      rw [Subsingleton.elim (1 : H) 0, map_zero] at h
      exact zero_ne_one h⟩
    infer_instance

variable [Coalgebra.IsCocomm ℤ_[p] H]

theorem exists_quotient_realising
    (M : Type) [AddCommGroup M]
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (act : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → M → M)
    (hact : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H, g h = σ (f h)) → e g = act σ (e f))
    (N' : AddSubgroup M) (hN' : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : M), x ∈ N' → act σ x ∈ N') :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B) (_ : Module.Flat ℤ_[p] B)
      (_ : Coalgebra.IsCocomm ℤ_[p] B) (π : H →ₐc[ℤ_[p]] B) (_ : Function.Surjective π)
      (eB : WithConv (B →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ↥N'),
      (∀ g : WithConv (B →ₐ[ℤ_[p]] PadicAlgCl p),
        ((eB g : ↥N') : M) = e (toConv ((ofConv g).comp (π : H →ₐ[ℤ_[p]] B)))) ∧
      (∀ f g, eB (f * g) = eB f + eB g) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (B →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ b : B, g b = σ (f b)) → ((eB g : ↥N') : M) = act σ ((eB f : ↥N') : M)) := by
  classical
  haveI : Finite (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) := finite_points p H
  haveI : Finite M := Finite.of_equiv _ e

  let N : Fin (1 + 1) → AddSubgroup M := fun i => if i = 0 then N' else ⊤
  have hN0 : N 0 = N' := rfl
  have hN1 : N (Fin.last 1) = ⊤ := rfl
  obtain ⟨B, instCR, instHopf, π, φ, hft, hflat, hπ, hφ, hcomp, hbij, hpts, hcoc, hfin⟩ :=
    HopfAlgebra.exists_quotientFlag_of_galoisStableChain_of_fixedPoints (K := ℚ_[p]) ℤ_[p]
      (algebraMap_padicInt_injective p) (hfix_padicInt p) H M e he act hact 1 N
      (fun i => by
        have hi : i = 0 := Fin.eq_zero i
        subst hi
        intro x _
        show x ∈ N (Fin.succ 0)
        show x ∈ (⊤ : AddSubgroup M)
        exact AddSubgroup.mem_top x)
      hN1
      (fun i σ x hx => by
        by_cases hi : i = 0
        · subst hi; exact hN' σ x hx
        · have : N i = ⊤ := if_neg hi
          rw [this]; exact AddSubgroup.mem_top _)
  letI := instCR 0
  letI := instHopf 0
  haveI : Module.Finite ℤ_[p] (B 0) := ((hfin inferInstance) 0).1
  haveI : Module.Flat ℤ_[p] (B 0) := hflat 0
  haveI : Coalgebra.IsCocomm ℤ_[p] (B 0) := hcoc inferInstance 0

  let pre : WithConv (B 0 →ₐ[ℤ_[p]] PadicAlgCl p) → WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
    fun g => toConv ((ofConv g).comp (π 0 : H →ₐ[ℤ_[p]] B 0))
  have hpre_inj : Function.Injective pre := by
    intro g₁ g₂ h
    apply WithConv.ext
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hπ 0 b
    have := congrArg (fun χ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) => ofConv χ a) h
    exact this
  have hpre_mem : ∀ g, e (pre g) ∈ N' := by
    intro g
    rw [← hN0]
    exact (hpts 0 ((ofConv g).comp (π 0 : H →ₐ[ℤ_[p]] B 0))).mp ⟨ofConv g, rfl⟩
  have hpre_surj : ∀ x ∈ N', ∃ g, e (pre g) = x := by
    intro x hx
    obtain ⟨f, rfl⟩ := e.surjective x
    rw [← hN0] at hx
    obtain ⟨g, hg⟩ := (hpts 0 (ofConv f)).mpr hx
    exact ⟨toConv g, by show e (toConv (g.comp _)) = _; rw [hg]⟩
  have hpre_mul : ∀ f g, pre (f * g) = pre f * pre g := by
    intro f g
    show toConv (AlgHom.comp (f * g).ofConv (π 0 : H →ₐ[ℤ_[p]] B 0)) = _
    rw [AlgHom.convMul_comp_bialgHom_distrib]
  let eB : WithConv (B 0 →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ↥N' :=
    Equiv.ofBijective (fun g => ⟨e (pre g), hpre_mem g⟩)
      ⟨fun g₁ g₂ h => hpre_inj (e.injective (congrArg Subtype.val h)),
       fun x => by
        obtain ⟨g, hg⟩ := hpre_surj x.1 x.2
        exact ⟨g, Subtype.ext hg⟩⟩
  refine ⟨B 0, instCR 0, instHopf 0, inferInstance, inferInstance, inferInstance, π 0, hπ 0, eB,
    fun g => rfl, fun f g => ?_, fun σ f g hfg => ?_⟩
  · apply Subtype.ext
    show e (pre (f * g)) = e (pre f) + e (pre g)
    rw [hpre_mul, he]
  · show e (pre g) = act σ (e (pre f))
    exact hact σ (pre f) (pre g) (fun h => hfg (π 0 h))

omit [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H] [Coalgebra.IsCocomm ℤ_[p] H] in

theorem forall_nnnorm_sub_counit_lt_one_of_comp {B : Type} [CommRing B] [HopfAlgebra ℤ_[p] B]
    (π : H →ₐc[ℤ_[p]] B) (hπ : Function.Surjective π) (g : B →ₐ[ℤ_[p]] PadicAlgCl p)
    (hred : ∀ h : H, ‖g (π h) - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit (R := ℤ_[p]) h)‖₊ < 1) :
    ∀ b : B, ‖g b - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit (R := ℤ_[p]) b)‖₊ < 1 := by
  intro b
  obtain ⟨h, rfl⟩ := hπ b
  rw [CoalgHomClass.counit_comp_apply]
  exact hred h

end S17L3

end

open S17L3 WithConv in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    (M : Type) [AddCommGroup M]
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
        ∀ x ∈ N i.succ, act σ x - x ∈ N i.castSucc) :
    ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      ∀ x : M, act σ x = x := by
  classical
  intro σ hσ x

  obtain ⟨K, hKmem, hKstab, hKdisp⟩ :=
    HopfAlgebra.exists_addSubgroup_forall_nnnorm_sub_counit_lt_one_padicInt p H M e he act hact

  have collapse : ∀ i : Fin n, ∀ y ∈ K, y ∈ N i.succ → y ∈ N i.castSucc := by
    intro i y hyK hyN
    obtain ⟨B, _, _, _, _, _, π, hπ, eB, heBval, heB, hactB⟩ :=
      exists_quotient_realising p H M e he act hact (N i.succ) (hstab i.succ)

    obtain ⟨f, hfy, hfred⟩ := (hKmem y).mp hyK
    obtain ⟨g, hg⟩ := eB.surjective ⟨y, hyN⟩
    have hgf : toConv ((ofConv g).comp (π : H →ₐ[ℤ_[p]] B)) = f := by
      apply e.injective
      rw [← heBval, hg, hfy]
    have hgred : ∀ b : B, ‖g b - algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit (R := ℤ_[p]) b)‖₊ < 1 := by
      refine forall_nnnorm_sub_counit_lt_one_of_comp p H π hπ (ofConv g) (fun h => ?_)
      have := hfred h
      rw [← hgf] at this
      exact this

    let actB : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ↥(N i.succ) → ↥(N i.succ) :=
      fun τ z => ⟨act τ z, hstab i.succ τ z z.2⟩
    have hactB' : ∀ (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f' g' : WithConv (B →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ b : B, g' b = τ (f' b)) → eB g' = actB τ (eB f') :=
      fun τ f' g' hfg => Subtype.ext (hactB τ f' g' hfg)
    let W : AddSubgroup ↥(N i.succ) := (N i.castSucc).comap (N i.succ).subtype
    have hW : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ z : ↥(N i.succ), actB τ z - z ∈ W := by
      intro τ hτ z
      show ((actB τ z - z : ↥(N i.succ)) : M) ∈ N i.castSucc
      rw [AddSubgroup.coe_sub]
      exact hstep i τ hτ z z.2
    have key := HopfAlgebra.mem_of_forall_nnnorm_sub_counit_lt_one_of_forall_inertia_displacement_mem_padicInt
      p hp2 B ↥(N i.succ) eB heB actB hactB' W hW g hgred
    have : ((eB g : ↥(N i.succ)) : M) ∈ N i.castSucc := key
    rw [hg] at this
    exact this

  have hd : act σ x - x ∈ K := hKdisp σ hσ x
  have hall : ∀ i : Fin (n + 1), act σ x - x ∈ N i := by
    intro i
    induction i using Fin.reverseInduction with
    | last => rw [htop]; exact AddSubgroup.mem_top _
    | cast i ih => exact collapse i _ hd ih
  have h0 := hall 0
  rw [hbot, AddSubgroup.mem_bot, sub_eq_zero] at h0
  exact h0

end S_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt
end P2MW
export P2MW.S_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt (solution)

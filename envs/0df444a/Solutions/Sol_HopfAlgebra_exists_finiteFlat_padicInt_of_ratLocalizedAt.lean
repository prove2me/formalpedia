-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_padicInt_of_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:52.885391+00:00
-- url     : https://prove2.me/submissions/6b5dd3d8-1dd9-4101-bd83-3c8535a0808c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Coalgebra.TensorProduct PadicInt

namespace HopfAlgebra

/-- Completion preserves a finite-flat Hopf model and its prescribed global point action. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime]
    {N : Type} [AddCommGroup N]
    (act : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N → N)
    (H0 : Type) [CommRing H0] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H0]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H0]
    [Module.Flat (GaloisRep.ratLocalizedAt p) H0]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H0]
    (e0 : WithConv (H0 →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he0_add : ∀ f g, e0 (f * g) = e0 f + e0 g)
    (he0_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H0 →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H0, g h = σ (f h)) → e0 g = act σ (e0 f)) :
    groupCohomology.IsFiniteFlatRepresentation p
      (fun σ => act (localGaloisToGlobal p σ)) := by
  classical
  have norm_cast_le_one (p : ℕ) [Fact p.Prime] (r : GaloisRep.ratLocalizedAt p) :
      ‖(algebraMap ℚ ℚ_[p] (r : ℚ))‖ ≤ 1 := by
    obtain ⟨r, hr⟩ := r
    have hden : Nat.Coprime r.den p := hr
    change ‖(algebraMap ℚ ℚ_[p] r)‖ ≤ 1
    have hr' : (algebraMap ℚ ℚ_[p] r) = ((r.num : ℚ_[p]) / (r.den : ℚ_[p])) := by
      rw [eq_ratCast, Rat.cast_def]
    rw [hr', norm_div]
    have hd : ‖(r.den : ℚ_[p])‖ = 1 := (Padic.norm_natCast_eq_one_iff).mpr (Nat.Coprime.symm hden)
    rw [hd, div_one]
    exact Padic.norm_int_le_one r.num
  let toPadicInt (p : ℕ) [Fact p.Prime] : GaloisRep.ratLocalizedAt p →+* ℤ_[p] := {
    toFun r := ⟨algebraMap ℚ ℚ_[p] (r : ℚ), norm_cast_le_one p r⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change (algebraMap ℚ ℚ_[p]) ((a : ℚ) * (b : ℚ)) =
        (algebraMap ℚ ℚ_[p]) (a : ℚ) * (algebraMap ℚ ℚ_[p]) (b : ℚ)
      exact map_mul _ _ _
    map_zero' := by apply Subtype.ext; simp
    map_add' a b := by
      apply Subtype.ext
      change (algebraMap ℚ ℚ_[p]) ((a : ℚ) + (b : ℚ)) =
        (algebraMap ℚ ℚ_[p]) (a : ℚ) + (algebraMap ℚ ℚ_[p]) (b : ℚ)
      exact map_add _ _ _
  }
  letI : Algebra (GaloisRep.ratLocalizedAt p) ℤ_[p] := (toPadicInt p).toAlgebra
  have algebraMap_R_Qpb (r : GaloisRep.ratLocalizedAt p) :
      algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r
        = algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (r : ℚ)) := by
    have h1 : algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r = algebraMap ℚ (PadicAlgCl p) (r : ℚ) := rfl
    rw [h1, eq_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), ← eq_ratCast (algebraMap ℚ ℚ_[p])]
  have algebraMap_toPadicInt (r : GaloisRep.ratLocalizedAt p) :
      algebraMap ℤ_[p] (PadicAlgCl p) (toPadicInt p r) = algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r := by
    rw [algebraMap_R_Qpb]; rfl
  letI : @IsScalarTower (GaloisRep.ratLocalizedAt p) ℤ_[p] (PadicAlgCl p)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
    constructor
    intro r z x
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
      show (algebraMap (GaloisRep.ratLocalizedAt p) ℤ_[p]) r = toPadicInt p r from rfl, algebraMap_toPadicInt]
  have padicEmbedding_algebraMap (r : GaloisRep.ratLocalizedAt p) :
      padicEmbedding p (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r)
        = algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r := by
    have h1 : algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) r
        = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl
    have h2 : algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p) r = algebraMap ℚ (PadicAlgCl p) (r : ℚ) := rfl
    rw [h1, h2, AlgHom.commutes]
  let ptsBC :
      ((ℤ_[p] ⊗[GaloisRep.ratLocalizedAt p] H0) →ₐ[ℤ_[p]] PadicAlgCl p) ≃
        (H0 →ₐ[GaloisRep.ratLocalizedAt p] PadicAlgCl p) :=
    { toFun := fun F => (F.restrictScalars (GaloisRep.ratLocalizedAt p)).comp Algebra.TensorProduct.includeRight
      invFun := fun g => Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] (PadicAlgCl p)) g (fun _ _ => Commute.all _ _)
      left_inv := fun F => by
        apply Algebra.TensorProduct.ext'
        intro a h
        simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
          Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply]
        rw [show a ⊗ₜ[GaloisRep.ratLocalizedAt p] h = (a ⊗ₜ 1) * (1 ⊗ₜ h) from by simp, map_mul]
        congr 1
        rw [show (a ⊗ₜ[GaloisRep.ratLocalizedAt p] (1 : H0)) = algebraMap ℤ_[p] _ a from by
          simp [Algebra.TensorProduct.algebraMap_apply], AlgHom.commutes]
      right_inv := fun g => by
        ext h
        simp [Algebra.TensorProduct.lift_tmul] }
  let reprBC {h : H0} {ι𝓡 : Type} (𝓡 : Coalgebra.Repr (GaloisRep.ratLocalizedAt p) h ι𝓡) :
      Coalgebra.Repr ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[GaloisRep.ratLocalizedAt p] h) ι𝓡 := {
    index := 𝓡.index
    left i := (1 : ℤ_[p]) ⊗ₜ 𝓡.left i
    right i := (1 : ℤ_[p]) ⊗ₜ 𝓡.right i
    eq := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq, TensorProduct.tmul_sum, map_sum]
      simp
  }
  have ptsBC_mul (F G : WithConv ((ℤ_[p] ⊗[GaloisRep.ratLocalizedAt p] H0) →ₐ[ℤ_[p]] PadicAlgCl p)) :
      ptsBC (F * G).ofConv
        = (WithConv.toConv (ptsBC F.ofConv) * WithConv.toConv (ptsBC G.ofConv)).ofConv := by
    apply AlgHom.ext
    intro h
    let 𝓡 := Coalgebra.Repr.arbitrary (GaloisRep.ratLocalizedAt p) h

    have hR : (WithConv.toConv (ptsBC F.ofConv) * WithConv.toConv (ptsBC G.ofConv)).ofConv h
        = ∑ i ∈ 𝓡.index, ptsBC F.ofConv (𝓡.left i) * ptsBC G.ofConv (𝓡.right i) := by
      have key := AlgHom.toLinearMap_convMul (WithConv.toConv (ptsBC F.ofConv)) (WithConv.toConv (ptsBC G.ofConv))
      have := congrArg (fun L => (WithConv.ofConv L) h) key
      simpa [Coalgebra.Repr.convMul_apply 𝓡] using this

    have hL : (F * G).ofConv ((1 : ℤ_[p]) ⊗ₜ h)
        = ∑ i ∈ 𝓡.index, F.ofConv ((1 : ℤ_[p]) ⊗ₜ 𝓡.left i) * G.ofConv ((1 : ℤ_[p]) ⊗ₜ 𝓡.right i) := by
      have key := AlgHom.toLinearMap_convMul F G
      have := congrArg (fun L => (WithConv.ofConv L) ((1 : ℤ_[p]) ⊗ₜ[GaloisRep.ratLocalizedAt p] h)) key
      simp [Coalgebra.Repr.convMul_apply (reprBC 𝓡)] at this
      exact this
    show (F * G).ofConv (Algebra.TensorProduct.includeRight h) = _
    rw [Algebra.TensorProduct.includeRight_apply, hL, hR]
    rfl
  let embQ : (AlgebraicClosure ℚ) →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p) :=
    { (padicEmbedding p).toRingHom with
      commutes' := fun r => by
        change padicEmbedding p (((r : ℚ) : (AlgebraicClosure ℚ))) = ((r : ℚ) : (PadicAlgCl p))
        exact map_ratCast (padicEmbedding p) (r : ℚ) }
  have embQ_apply (x : (AlgebraicClosure ℚ)) : embQ x = padicEmbedding p x := rfl
  have embQ_injective : Function.Injective (embQ) := (padicEmbedding p).injective
  have exists_embQ_eq_apply (φ : H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p)) (h : H0) : ∃ y : (AlgebraicClosure ℚ), embQ y = φ h := by
    have hint : IsIntegral (GaloisRep.ratLocalizedAt p) h := Algebra.IsIntegral.isIntegral h
    obtain ⟨P, hPmonic, hPeval⟩ := hint
    have hP0 : P ≠ 0 := hPmonic.ne_zero

    have hroot : (P.map (algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p))).IsRoot (φ h) := by
      rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
        Polynomial.aeval_def, hPeval, map_zero]

    set g : Polynomial (AlgebraicClosure ℚ) := P.map (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) with hg
    have hsplit : g.Splits := IsAlgClosed.splits g
    have hroots := hsplit.roots_map (embQ).toRingHom
    have hgmap : g.map (embQ).toRingHom = P.map (algebraMap (GaloisRep.ratLocalizedAt p) (PadicAlgCl p)) := by
      rw [hg, Polynomial.map_map]
      congr 1
      ext r
      exact (embQ).commutes r
    have hmem : φ h ∈ (g.map (embQ).toRingHom).roots := by
      rw [hgmap, Polynomial.mem_roots (Polynomial.map_monic_ne_zero hPmonic)]
      exact hroot
    rw [hroots, Multiset.mem_map] at hmem
    obtain ⟨y, -, hy⟩ := hmem
    exact ⟨y, hy⟩
  let lift (φ : H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p)) : H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ) := {
    toFun h := (exists_embQ_eq_apply φ h).choose
    map_one' := embQ_injective (by rw [(exists_embQ_eq_apply φ 1).choose_spec, map_one, map_one])
    map_mul' a b := embQ_injective (by
      rw [(exists_embQ_eq_apply φ (a * b)).choose_spec, map_mul, map_mul,
        (exists_embQ_eq_apply φ a).choose_spec, (exists_embQ_eq_apply φ b).choose_spec])
    map_zero' := embQ_injective (by rw [(exists_embQ_eq_apply φ 0).choose_spec, map_zero, map_zero])
    map_add' a b := embQ_injective (by
      rw [(exists_embQ_eq_apply φ (a + b)).choose_spec, map_add, map_add,
        (exists_embQ_eq_apply φ a).choose_spec, (exists_embQ_eq_apply φ b).choose_spec])
    commutes' r := embQ_injective (by
      rw [(exists_embQ_eq_apply φ (algebraMap (GaloisRep.ratLocalizedAt p) H0 r)).choose_spec, AlgHom.commutes, AlgHom.commutes])
  }
  have embQ_lift (φ : H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p)) (h : H0) : embQ (lift φ h) = φ h :=
    (exists_embQ_eq_apply φ h).choose_spec
  have embQ_comp_lift (φ : H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p)) : (embQ).comp (lift φ) = φ :=
    AlgHom.ext fun h => embQ_lift φ h
  have lift_embQ_comp (ψ : H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ)) : lift ((embQ).comp ψ) = ψ :=
    AlgHom.ext fun h => embQ_injective (by rw [embQ_lift]; rfl)
  let ptsQbar : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p)) ≃ WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ)) := {
    toFun F := WithConv.toConv (lift (WithConv.ofConv F))
    invFun f := WithConv.toConv ((embQ).comp (WithConv.ofConv f))
    left_inv F := by simp [embQ_comp_lift]
    right_inv f := by simp [lift_embQ_comp]
  }
  have embQ_ptsQbar_apply (F : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p))) (h : H0) : embQ (ptsQbar F h) = F h :=
    embQ_lift _ h
  have ptsQbar_symm_apply (f : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ))) (h : H0) : ptsQbar.symm f h = embQ (f h) := rfl
  have ptsQbar_apply_of_forall_eq (τ : (PadicAlgCl p) ≃ₐ[ℚ_[p]] (PadicAlgCl p)) (F G : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p)))
      (hFG : ∀ h : H0, G h = τ (F h)) (h : H0) :
      ptsQbar G h = localGaloisToGlobal p τ (ptsQbar F h) := by
    apply embQ_injective
    rw [embQ_ptsQbar_apply, hFG, embQ_apply, padicEmbedding_localGaloisToGlobal, ← embQ_apply,
      embQ_ptsQbar_apply]
  have convMul_apply_repr {L : Type} [CommRing L] [Algebra (GaloisRep.ratLocalizedAt p) L] (f g : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] L))
      {h : H0} {ι𝓡 : Type} (𝓡 : Coalgebra.Repr (GaloisRep.ratLocalizedAt p) h ι𝓡) :
      (f * g) h = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
    have := congrArg (fun (φ : WithConv (H0 →ₗ[(GaloisRep.ratLocalizedAt p)] L)) => (WithConv.ofConv φ) h)
      (AlgHom.toLinearMap_convMul f g)
    simp only [WithConv.ofConv_toConv, AlgHom.toLinearMap_apply] at this
    rw [this, Coalgebra.Repr.convMul_apply 𝓡]
    rfl
  have ptsQbar_symm_mul (f g : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ))) :
      (ptsQbar.symm (f * g) : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p))) = ptsQbar.symm f * ptsQbar.symm g := by
    classical
    have hext : ∀ (F G : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p))), (∀ h : H0, F h = G h) → F = G := by
      intro F G hFG
      have : WithConv.ofConv F = WithConv.ofConv G := AlgHom.ext hFG
      simpa using congrArg WithConv.toConv this
    apply hext
    intro h
    let 𝓡 := Coalgebra.Repr.arbitrary (GaloisRep.ratLocalizedAt p) h
    rw [ptsQbar_symm_apply, convMul_apply_repr f g 𝓡, convMul_apply_repr _ _ 𝓡, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ptsQbar_symm_apply, ptsQbar_symm_apply]
  have ptsQbar_mul (F G : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (PadicAlgCl p))) :
      (ptsQbar (F * G) : WithConv (H0 →ₐ[(GaloisRep.ratLocalizedAt p)] (AlgebraicClosure ℚ))) = ptsQbar F * ptsQbar G := by
    apply ptsQbar.symm.injective
    rw [Equiv.symm_apply_apply, ptsQbar_symm_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  classical
  let HB := ℤ_[p] ⊗[GaloisRep.ratLocalizedAt p] H0
  let E : WithConv (HB →ₐ[ℤ_[p]] PadicAlgCl p) ≃ N :=
    (((Equiv.mk WithConv.ofConv WithConv.toConv (fun _ => rfl) (fun _ => rfl)).trans
      (ptsBC)).trans
      (Equiv.mk WithConv.toConv WithConv.ofConv (fun _ => rfl) (fun _ => rfl))).trans
      (ptsQbar.trans e0)
  have hE : ∀ F : WithConv (HB →ₐ[ℤ_[p]] PadicAlgCl p),
      E F = e0 (ptsQbar
        (WithConv.toConv (ptsBC (WithConv.ofConv F)))) := fun _ => rfl
  refine ⟨HB, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, E, ?_, ?_⟩
  · intro F G
    rw [hE, hE, hE, ptsBC_mul, WithConv.toConv_ofConv,
      ptsQbar_mul, he0_add]
  · intro σ F G hFG
    rw [hE, hE]
    apply he0_act
    intro h
    apply ptsQbar_apply_of_forall_eq σ
    intro h'
    exact hFG _

end HopfAlgebra

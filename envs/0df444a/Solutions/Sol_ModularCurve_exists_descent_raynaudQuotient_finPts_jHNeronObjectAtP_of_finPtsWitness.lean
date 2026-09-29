-- Prove2me | solution 1 for ModularCurve.exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/af409bc5-514a-5f81-b99c-8be548ec7d4d

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PDivisibleGroup_eq_of_forall_point_toAlgHom_apply_eq
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_PDivisibleGroup_finite_point_and_natCard_point_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open scoped TensorProduct

namespace QBL3

variable (R : Type) [CommRing R] [IsLocalRing R] (k : Type) [Field k] [Algebra R k]

theorem isLocalHom_of_surjective (hk : Function.Surjective (algebraMap R k)) : IsLocalHom (algebraMap R k) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal R := hna
  have hker : RingHom.ker (algebraMap R k) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap R k) hk)
  rw [← hker, RingHom.mem_ker] at hmem
  rw [hmem] at ha
  exact not_isUnit_zero ha

noncomputable def resLin (hk : Function.Surjective (algebraMap R k)) : IsLocalRing.ResidueField R →ₗ[R] k :=
  haveI := isLocalHom_of_surjective R k hk
  { toFun := IsLocalRing.ResidueField.lift (algebraMap R k)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      change IsLocalRing.ResidueField.lift (algebraMap R k) (r • IsLocalRing.residue R x) =
        r • IsLocalRing.ResidueField.lift (algebraMap R k) (IsLocalRing.residue R x)
      have hs : r • IsLocalRing.residue R x = IsLocalRing.residue R (r * x) := by
        rw [map_mul]; rfl
      rw [hs, IsLocalRing.ResidueField.lift_residue_apply, IsLocalRing.ResidueField.lift_residue_apply, map_mul,
        Algebra.smul_def] }

theorem resLin_residue (hk : Function.Surjective (algebraMap R k)) (r : R) :
    resLin R k hk (IsLocalRing.residue R r) = algebraMap R k r := by
  haveI := isLocalHom_of_surjective R k hk
  exact IsLocalRing.ResidueField.lift_residue_apply _ r

theorem resLin_bijective (hk : Function.Surjective (algebraMap R k)) : Function.Bijective (resLin R k hk) := by
  haveI := isLocalHom_of_surjective R k hk
  refine ⟨(IsLocalRing.ResidueField.lift (algebraMap R k)).injective, fun y => ?_⟩
  obtain ⟨r, rfl⟩ := hk y
  exact ⟨IsLocalRing.residue R r, resLin_residue R k hk r⟩

end QBL3

theorem QB.exists_retraction_of_injective_baseChange (R : Type) [CommRing R] [IsLocalRing R]
    (k : Type) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    {M N : Type} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
    (f : M →ₗ[R] N) (hf : Function.Injective (f.baseChange k)) :
    ∃ ρ : N →ₗ[R] M, ρ ∘ₗ f = LinearMap.id := by
  refine (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr ?_
  let e : IsLocalRing.ResidueField R ≃ₗ[R] k := LinearEquiv.ofBijective _ (QBL3.resLin_bijective R k hk)
  have hnat : ∀ x : IsLocalRing.ResidueField R ⊗[R] M,
      (e.toLinearMap.rTensor N) (f.lTensor (IsLocalRing.ResidueField R) x) = f.lTensor k ((e.toLinearMap.rTensor M) x) := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  intro x y hxy
  have h := congrArg (e.toLinearMap.rTensor N) hxy
  rw [hnat, hnat] at h
  have h2 : (e.toLinearMap.rTensor M) x = (e.toLinearMap.rTensor M) y := hf h
  exact (LinearEquiv.rTensor M e).injective h2

open scoped TensorProduct

namespace QBL2

variable (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
  [Algebra O (AlgebraicClosure ℚ)] (v : ℕ)

noncomputable abbrev evalAt (x : H.Point (AlgebraicClosure ℚ) v) : AlgebraicClosure ℚ ⊗[O] H.level v →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ :=
  Algebra.TensorProduct.lift (AlgHom.id (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) (PDivisibleGroup.Point.toAlgHom x) (fun _ _ => Commute.all _ _)

theorem exists_evalAt_eq (ψ : AlgebraicClosure ℚ ⊗[O] H.level v →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ) :
    ∃ x : H.Point (AlgebraicClosure ℚ) v, evalAt p H v x = ψ := by
  refine ⟨PDivisibleGroup.Point.ofAlgHom ((ψ.restrictScalars O).comp Algebra.TensorProduct.includeRight), ?_⟩
  apply Algebra.TensorProduct.ext'
  intro a b
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
  change a * ψ ((1 : AlgebraicClosure ℚ) ⊗ₜ[O] b) = ψ (a ⊗ₜ[O] b)
  rw [← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

noncomputable def ev : AlgebraicClosure ℚ ⊗[O] H.level v →ₗ[AlgebraicClosure ℚ] (H.Point (AlgebraicClosure ℚ) v → AlgebraicClosure ℚ) where
  toFun τ x := evalAt p H v x τ
  map_add' τ τ' := funext fun x => map_add _ _ _
  map_smul' c τ := funext fun x => by
    rw [RingHom.id_apply, Pi.smul_apply, map_smul]

theorem ev_apply (τ : AlgebraicClosure ℚ ⊗[O] H.level v) (x : H.Point (AlgebraicClosure ℚ) v) : ev p H v τ x = evalAt p H v x τ := rfl

theorem ev_injective : Function.Injective (ev p H v) := by
  classical
  let A := AlgebraicClosure ℚ ⊗[O] H.level v
  haveI : IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero (AlgebraicClosure ℚ) A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite (AlgebraicClosure ℚ) A
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro τ hτ
  rw [LinearMap.mem_ker] at hτ

  have hmax : ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → τ ∈ 𝔪 := by
    intro 𝔪 h𝔪
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) (A ⧸ 𝔪) := Algebra.IsIntegral.of_finite _ _
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := A ⧸ 𝔪)
    let e : (A ⧸ 𝔪) ≃ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ := (AlgEquiv.ofBijective (Algebra.ofId (AlgebraicClosure ℚ) (A ⧸ 𝔪)) hbij).symm
    let ψ : A →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ := (e : (A ⧸ 𝔪) →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ).comp (Ideal.Quotient.mkₐ (AlgebraicClosure ℚ) 𝔪)
    obtain ⟨x, hx⟩ := exists_evalAt_eq p H v ψ
    have h0 : ψ τ = 0 := by rw [← hx]; exact congrFun hτ x
    have h1 : Ideal.Quotient.mkₐ (AlgebraicClosure ℚ) 𝔪 τ = 0 := by
      have := congrArg e.symm h0
      rwa [map_zero, show e.symm (ψ τ) = Ideal.Quotient.mkₐ (AlgebraicClosure ℚ) 𝔪 τ from e.symm_apply_apply _] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hjac : τ ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro 𝔪 ⟨-, h𝔪⟩
    exact hmax 𝔪 h𝔪
  rw [IsArtinianRing.jacobson_eq_radical] at hjac
  have hnil : τ ∈ nilradical A := hjac
  rw [nilradical_eq_zero] at hnil
  exact hnil

theorem ev_surjective : Function.Surjective (ev p H v) := by
  classical
  haveI : Finite (H.Point (AlgebraicClosure ℚ) v) := (PDivisibleGroup.finite_point_and_natCard_point_eq_pow p H (AlgebraicClosure ℚ) v).1
  letI : Fintype (H.Point (AlgebraicClosure ℚ) v) := Fintype.ofFinite _
  have hcard := (PDivisibleGroup.finite_point_and_natCard_point_eq_pow p H (AlgebraicClosure ℚ) v).2
  haveI : Nontrivial O := (algebraMap O (AlgebraicClosure ℚ)).domain_nontrivial
  have hdim : Module.finrank (AlgebraicClosure ℚ) (AlgebraicClosure ℚ ⊗[O] H.level v) = Module.finrank (AlgebraicClosure ℚ) (H.Point (AlgebraicClosure ℚ) v → AlgebraicClosure ℚ) := by
    rw [Module.finrank_baseChange, H.finrank_level, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (ev_injective p H v)

end QBL2

theorem QB.eval_baseChange_injective_and_surjective (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] {h : ℕ}
    (H : PDivisibleGroup O p h) [Algebra O (AlgebraicClosure ℚ)] (v : ℕ) :
    (∀ τ : AlgebraicClosure ℚ ⊗[O] H.level v,
      (∀ x : H.Point (AlgebraicClosure ℚ) v,
        Algebra.TensorProduct.lift (AlgHom.id (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) (PDivisibleGroup.Point.toAlgHom x)
          (fun _ _ => Commute.all _ _) τ = 0) → τ = 0) ∧
    (∀ φ : H.Point (AlgebraicClosure ℚ) v → AlgebraicClosure ℚ, ∃ τ : AlgebraicClosure ℚ ⊗[O] H.level v, ∀ x : H.Point (AlgebraicClosure ℚ) v,
        Algebra.TensorProduct.lift (AlgHom.id (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) (PDivisibleGroup.Point.toAlgHom x)
          (fun _ _ => Commute.all _ _) τ = φ x) := by
  refine ⟨fun τ hτ => QBL2.ev_injective p H v (funext fun x => ?_), fun φ => ?_⟩
  · rw [QBL2.ev_apply, map_zero]; exact hτ x
  · obtain ⟨τ, hτ⟩ := QBL2.ev_surjective p H v φ
    exact ⟨τ, fun x => by rw [← QBL2.ev_apply, hτ]⟩

open scoped TensorProduct

namespace QB

open PDivisibleGroup

variable {Rh : Type} [CommRing Rh] [IsDomain Rh] [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  {p : ℕ} [Fact p.Prime] {h hB : ℕ} (𝒢 : PDivisibleGroup Rh p h) (ℬ : PDivisibleGroup Rh p hB) (v : ℕ)
  (ψ : ℬ.level v →ₐc[Rh] 𝒢.level v)

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable def rPt : 𝒢.Point ℚ̄ v →* ℬ.Point ℚ̄ v := Hopf.convCompMonoidHom ℚ̄ ψ

omit [IsDomain Rh] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] in
theorem rPt_apply (x : 𝒢.Point ℚ̄ v) :
    rPt 𝒢 ℬ v ψ x = Point.ofAlgHom ((Point.toAlgHom x).comp (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v)) := rfl

noncomputable def sPt (w : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.Point ℚ̄ v →* 𝒢.Point ℚ̄ v := Hopf.convCompMonoidHom ℚ̄ w

omit [IsDomain Rh] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] in
theorem sPt_apply (w : 𝒢.level v →ₐc[Rh] 𝒢.level v) (x : 𝒢.Point ℚ̄ v) :
    sPt 𝒢 v w x = Point.ofAlgHom ((Point.toAlgHom x).comp (w : 𝒢.level v →ₐ[Rh] 𝒢.level v)) := rfl

theorem injective_of_forall_exists (hψsurj : ∀ b : ℬ.Point ℚ̄ v, ∃ x : 𝒢.Point ℚ̄ v, rPt 𝒢 ℬ v ψ x = b) :
    Function.Injective ψ := by
  intro b b' hbb'
  refine PDivisibleGroup.eq_of_forall_point_toAlgHom_apply_eq p
    (FaithfulSMul.algebraMap_injective Rh ℚ̄) ℬ v b b' fun y => ?_
  obtain ⟨x, rfl⟩ := hψsurj y
  change Point.toAlgHom x (ψ b) = Point.toAlgHom x (ψ b')
  rw [hbb']

noncomputable def evG (x : 𝒢.Point ℚ̄ v) : ℚ̄ ⊗[Rh] 𝒢.level v →ₐ[ℚ̄] ℚ̄ :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ̄ ℚ̄) (Point.toAlgHom x) (fun _ _ => Commute.all _ _)

noncomputable def evB (y : ℬ.Point ℚ̄ v) : ℚ̄ ⊗[Rh] ℬ.level v →ₐ[ℚ̄] ℚ̄ :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ̄ ℚ̄) (Point.toAlgHom y) (fun _ _ => Commute.all _ _)

omit [IsDomain Rh] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] in
theorem evG_tmul (x : 𝒢.Point ℚ̄ v) (s : ℚ̄) (a : 𝒢.level v) : evG 𝒢 v x (s ⊗ₜ a) = s * Point.toAlgHom x a := by
  simp [evG]

omit [IsDomain Rh] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] in
theorem evB_tmul (y : ℬ.Point ℚ̄ v) (s : ℚ̄) (b : ℬ.level v) : evB ℬ v y (s ⊗ₜ b) = s * Point.toAlgHom y b := by
  simp [evB]

omit [IsDomain Rh] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] in

theorem evG_baseChange (x : 𝒢.Point ℚ̄ v) (τ : ℚ̄ ⊗[Rh] ℬ.level v) :
    evG 𝒢 v x ((ψ : ℬ.level v →ₗ[Rh] 𝒢.level v).baseChange ℚ̄ τ) = evB ℬ v (rPt 𝒢 ℬ v ψ x) τ := by
  induction τ using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [LinearMap.baseChange_tmul, evG_tmul, evB_tmul]
    rfl
  | add x' y' hx hy => rw [map_add, map_add, map_add, hx, hy]

omit [IsDomain Rh] [Algebra Rh ℚ̄] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] in
theorem amap_eq_lmap {A B : Type} [CommRing A] [CommRing B] [Algebra Rh A] [Algebra Rh B]
    (f : A →ₐ[Rh] B) (t : A ⊗[Rh] A) :
    Algebra.TensorProduct.map f f t = TensorProduct.map f.toLinearMap f.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_comp_eq_comp
    (hL2B : ∀ φ : ℬ.Point ℚ̄ v → ℚ̄, ∃ τ : ℚ̄ ⊗[Rh] ℬ.level v, ∀ y, evB ℬ v y τ = φ y)
    (hL2G : ∀ σ : ℚ̄ ⊗[Rh] 𝒢.level v, (∀ x, evG 𝒢 v x σ = 0) → σ = 0)
    (ρ : 𝒢.level v →ₗ[Rh] ℬ.level v) (hρ : ρ ∘ₗ (ψ : ℬ.level v →ₗ[Rh] 𝒢.level v) = LinearMap.id)
    (Tor : Set (𝒢.Point ℚ̄ v))
    (hψker : ∀ x : 𝒢.Point ℚ̄ v, rPt 𝒢 ℬ v ψ x = 1 ↔ x ∈ Tor)
    (hψsurj : ∀ b : ℬ.Point ℚ̄ v, ∃ x : 𝒢.Point ℚ̄ v, rPt 𝒢 ℬ v ψ x = b)
    (w : 𝒢.level v →ₐc[Rh] 𝒢.level v) (hw : ∀ x ∈ Tor, sPt 𝒢 v w x ∈ Tor) :
    ∃ wB : ℬ.level v →ₐc[Rh] ℬ.level v, w.comp ψ = ψ.comp wB := by
  classical
  have hinj : Function.Injective ψ := injective_of_forall_exists 𝒢 ℬ v ψ hψsurj

  have hfib : ∀ x x' : 𝒢.Point ℚ̄ v, rPt 𝒢 ℬ v ψ x = rPt 𝒢 ℬ v ψ x' →
      rPt 𝒢 ℬ v ψ (sPt 𝒢 v w x) = rPt 𝒢 ℬ v ψ (sPt 𝒢 v w x') := by
    intro x x' hxx'
    have ht : x⁻¹ * x' ∈ Tor := (hψker _).mp (by rw [map_mul, map_inv, hxx', inv_mul_cancel])
    have hst : rPt 𝒢 ℬ v ψ (sPt 𝒢 v w (x⁻¹ * x')) = 1 := (hψker _).mpr (hw _ ht)
    have hx' : x' = x * (x⁻¹ * x') := by rw [mul_inv_cancel_left]
    conv_rhs => rw [hx']
    rw [map_mul, map_mul, hst, mul_one]

  have key : ∀ b : ℬ.level v, ψ (ρ (w (ψ b))) = w (ψ b) := by
    intro b

    let Φ : ℬ.Point ℚ̄ v → ℚ̄ := fun y => Point.toAlgHom (rPt 𝒢 ℬ v ψ (sPt 𝒢 v w (hψsurj y).choose)) b
    have hΦ : ∀ x : 𝒢.Point ℚ̄ v, Φ (rPt 𝒢 ℬ v ψ x) = Point.toAlgHom x (w (ψ b)) := by
      intro x
      have hc := (hψsurj (rPt 𝒢 ℬ v ψ x)).choose_spec
      change Point.toAlgHom (rPt 𝒢 ℬ v ψ (sPt 𝒢 v w (hψsurj (rPt 𝒢 ℬ v ψ x)).choose)) b = _
      rw [hfib _ _ hc]
      rfl
    obtain ⟨τ, hτ⟩ := hL2B Φ

    have hσ : (ψ : ℬ.level v →ₗ[Rh] 𝒢.level v).baseChange ℚ̄ τ = (1 : ℚ̄) ⊗ₜ[Rh] w (ψ b) := by
      rw [← sub_eq_zero]
      refine hL2G _ fun x => ?_
      rw [map_sub, evG_baseChange, hτ, hΦ, evG_tmul, one_mul, sub_self]

    have hτ' : τ = (1 : ℚ̄) ⊗ₜ[Rh] ρ (w (ψ b)) := by
      have h1 := congrArg (ρ.baseChange ℚ̄) hσ
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hρ, LinearMap.baseChange_id, LinearMap.id_apply,
        LinearMap.baseChange_tmul] at h1
      exact h1
    rw [hτ', LinearMap.baseChange_tmul] at hσ

    have hincl := Algebra.TensorProduct.includeRight_injective (R := Rh) (A := ℚ̄) (B := 𝒢.level v)
      (FaithfulSMul.algebraMap_injective Rh ℚ̄)
    exact hincl hσ

  let wBₐ : ℬ.level v →ₐ[Rh] ℬ.level v :=
    { toFun := fun b => ρ (w (ψ b))
      map_one' := hinj (by rw [key]; simp)
      map_mul' := fun b b' => hinj (by rw [key, map_mul, map_mul, map_mul, key, key])
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun b b' => by rw [map_add, map_add, map_add]
      commutes' := fun r => hinj (by rw [key]; simp [AlgHomClass.commutes]) }
  have hwB : ∀ b, ψ (wBₐ b) = w (ψ b) := fun b => key b
  have hwB' : (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v).comp wBₐ = (w : 𝒢.level v →ₐ[Rh] 𝒢.level v).comp (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v) :=
    AlgHom.ext hwB

  have hcounit : (Bialgebra.counitAlgHom Rh (ℬ.level v)).comp wBₐ = Bialgebra.counitAlgHom Rh (ℬ.level v) := by
    refine AlgHom.ext fun b => ?_
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      ← CoalgHomClass.counit_comp_apply ψ (wBₐ b), hwB, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]
  have hψψ : Function.Injective (Algebra.TensorProduct.map (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v) (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v)) := by
    have hcoe : ⇑(Algebra.TensorProduct.map (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v) (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
        ⇑(LinearMap.rTensor (𝒢.level v) (ψ : ℬ.level v →ₗ[Rh] 𝒢.level v) ∘ₗ
          LinearMap.lTensor (ℬ.level v) (ψ : ℬ.level v →ₗ[Rh] 𝒢.level v)) := by
      rw [LinearMap.rTensor_comp_lTensor]
      funext t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b b' => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hcoe, LinearMap.coe_comp]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hinj).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hinj)
  have hcomul : (Algebra.TensorProduct.map wBₐ wBₐ).comp (Bialgebra.comulAlgHom Rh (ℬ.level v)) =
      (Bialgebra.comulAlgHom Rh (ℬ.level v)).comp wBₐ := by
    refine AlgHom.ext fun b => hψψ ?_
    simp only [AlgHom.comp_apply]
    have hmm : ∀ t, Algebra.TensorProduct.map (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v) (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v)
        (Algebra.TensorProduct.map wBₐ wBₐ t) =
        Algebra.TensorProduct.map (w : 𝒢.level v →ₐ[Rh] 𝒢.level v) (w : 𝒢.level v →ₐ[Rh] 𝒢.level v)
          (Algebra.TensorProduct.map (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v) (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v) t) := by
      intro t
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hwB', Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
    have e1 : ∀ y : ℬ.level v, TensorProduct.map (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v).toLinearMap
        (ψ : ℬ.level v →ₐ[Rh] 𝒢.level v).toLinearMap (Coalgebra.comul (R := Rh) y) = Coalgebra.comul (R := Rh) (ψ y) :=
      fun y => CoalgHomClass.map_comp_comul_apply ψ y
    have e2 : ∀ z : 𝒢.level v, TensorProduct.map (w : 𝒢.level v →ₐ[Rh] 𝒢.level v).toLinearMap
        (w : 𝒢.level v →ₐ[Rh] 𝒢.level v).toLinearMap (Coalgebra.comul (R := Rh) z) = Coalgebra.comul (R := Rh) (w z) :=
      fun z => CoalgHomClass.map_comp_comul_apply w z
    rw [Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply, hmm, amap_eq_lmap, amap_eq_lmap, e1, e2,
      amap_eq_lmap, e1, hwB]
  refine ⟨BialgHom.ofAlgHom wBₐ hcounit hcomul, BialgHom.ext fun b => ?_⟩
  change w (ψ b) = ψ (wBₐ b)
  rw [hwB]

end QB

namespace QB

open PDivisibleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem coe_bmap_eq_baseChange {R : Type} [CommRing R] (k : Type) [CommRing k] [Algebra R k]
    {A B : Type} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B] (ψ : A →ₐc[R] B) :
    ⇑(Bialgebra.TensorProduct.map (BialgHom.id k k) ψ) = ⇑((ψ : A →ₗ[R] B).baseChange k) := by
  funext t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {Rh : Type} [CommRing Rh] [IsDomain Rh] [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
  {p : ℕ} [Fact p.Prime] [Algebra Rh (ZMod p)] {h hB : ℕ} (𝒢 : PDivisibleGroup Rh p h) (ℬ : PDivisibleGroup Rh p hB)

omit [IsDomain Rh] [FaithfulSMul Rh ℚ̄] [Fact p.Prime] [Algebra Rh (ZMod p)] in

theorem symm_mapsTo (v : ℕ) [Finite (𝒢.Point ℚ̄ v)] (Tor : Set (𝒢.Point ℚ̄ v)) (D : 𝒢.level v ≃ₐc[Rh] 𝒢.level v)
    (hD : ∀ x ∈ Tor, sPt 𝒢 v (D : 𝒢.level v →ₐc[Rh] 𝒢.level v) x ∈ Tor) :
    ∀ x ∈ Tor, sPt 𝒢 v (D.symm : 𝒢.level v →ₐc[Rh] 𝒢.level v) x ∈ Tor := by
  classical
  have hinv : ∀ y, sPt 𝒢 v (D : 𝒢.level v →ₐc[Rh] 𝒢.level v) (sPt 𝒢 v (D.symm : 𝒢.level v →ₐc[Rh] 𝒢.level v) y) = y := by
    intro y
    refine Point.ext fun a => ?_
    simp [sPt_apply]
  have hinv' : ∀ y, sPt 𝒢 v (D.symm : 𝒢.level v →ₐc[Rh] 𝒢.level v) (sPt 𝒢 v (D : 𝒢.level v →ₐc[Rh] 𝒢.level v) y) = y := by
    intro y
    refine Point.ext fun a => ?_
    simp [sPt_apply]
  have hinjD : Function.Injective (sPt 𝒢 v (D : 𝒢.level v →ₐc[Rh] 𝒢.level v)) :=
    Function.LeftInverse.injective hinv'
  have hfin : Tor.Finite := Set.toFinite Tor
  have hbij : Set.BijOn (sPt 𝒢 v (D : 𝒢.level v →ₐc[Rh] 𝒢.level v)) Tor Tor :=
    (hfin.injOn_iff_bijOn_of_mapsTo hD).mp (hinjD.injOn)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hbij.surjOn hy
  rw [← hxy, hinv']
  exact hx

theorem assemble
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v) (Tor : ∀ v : ℕ, Set (𝒢.Point ℚ̄ v))
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point ℚ̄ v), rPt 𝒢 ℬ v (ψ v) x = 1 ↔ x ∈ Tor v)
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point ℚ̄ v), ∃ x : 𝒢.Point ℚ̄ v, rPt 𝒢 ℬ v (ψ v) x = b)
    (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hut : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v)
    (hDpt : ∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
      (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v))
    (hutor : ∀ (v : ℕ), ∀ x ∈ Tor v, sPt 𝒢 v (u v) x ∈ Tor v)
    (hDptor : ∀ (v : ℕ), ∀ x ∈ Tor v, sPt 𝒢 v (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) x ∈ Tor v)
    (hjB : ∀ v, Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)))
    (hL2G : ∀ (v : ℕ) (σ : ℚ̄ ⊗[Rh] 𝒢.level v), (∀ x, evG 𝒢 v x σ = 0) → σ = 0)
    (hL2B : ∀ (v : ℕ) (φ : ℬ.Point ℚ̄ v → ℚ̄), ∃ τ : ℚ̄ ⊗[Rh] ℬ.level v, ∀ y, evB ℬ v y τ = φ y)
    (hL3 : ∀ (v : ℕ) (f : ℬ.level v →ₗ[Rh] 𝒢.level v), Function.Injective (f.baseChange (ZMod p)) →
      ∃ ρ : 𝒢.level v →ₗ[Rh] ℬ.level v, ρ ∘ₗ f = LinearMap.id)
    (hfin : ∀ v, Finite (𝒢.Point ℚ̄ v)) :
    ∃ (uB : ∀ v : ℕ, ℬ.level v →ₐc[Rh] ℬ.level v) (DB : ∀ v : ℕ, ℬ.level v ≃ₐc[Rh] ℬ.level v),
      (∀ v : ℕ, (u v).comp (ψ v) = (ψ v).comp (uB v)) ∧
      (∀ v : ℕ, (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (ψ v) = (ψ v).comp (DB v : ℬ.level v →ₐc[Rh] ℬ.level v)) ∧
      (∀ v : ℕ, (ℬ.transition v).comp (uB (v + 1)) = (uB v).comp (ℬ.transition v)) ∧
      (∀ v : ℕ, (ℬ.transition v).comp (DB (v + 1) : ℬ.level (v + 1) →ₐc[Rh] ℬ.level (v + 1)) =
        (DB v : ℬ.level v →ₐc[Rh] ℬ.level v).comp (ℬ.transition v)) := by
  classical
  have hinj : ∀ v, Function.Injective (ψ v) := fun v => injective_of_forall_exists 𝒢 ℬ v (ψ v) (hψsurj v)

  have hρ : ∀ v, ∃ ρ : 𝒢.level v →ₗ[Rh] ℬ.level v, ρ ∘ₗ (ψ v : ℬ.level v →ₗ[Rh] 𝒢.level v) = LinearMap.id := by
    intro v
    refine hL3 v _ ?_
    rw [← coe_bmap_eq_baseChange (ZMod p) (ψ v)]
    exact hjB v
  choose ρ hρ using hρ

  have EU := fun v => exists_comp_eq_comp 𝒢 ℬ v (ψ v) (hL2B v) (hL2G v) (ρ v) (hρ v) (Tor v) (hψker v) (hψsurj v)
    (u v) (hutor v)
  have ED := fun v => exists_comp_eq_comp 𝒢 ℬ v (ψ v) (hL2B v) (hL2G v) (ρ v) (hρ v) (Tor v) (hψker v) (hψsurj v)
    (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) (hDptor v)
  have ED' := fun v => exists_comp_eq_comp 𝒢 ℬ v (ψ v) (hL2B v) (hL2G v) (ρ v) (hρ v) (Tor v) (hψker v) (hψsurj v)
    ((Dp v).symm : 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (by haveI := hfin v; exact symm_mapsTo 𝒢 v (Tor v) (Dp v) (hDptor v))
  choose uB huB using EU
  choose dB hdB using ED
  choose dB' hdB' using ED'

  have h1 : ∀ v, (dB v).comp (dB' v) = BialgHom.id Rh (ℬ.level v) := by
    intro v
    refine BialgHom.ext fun b => hinj v ?_
    have e1 := BialgHom.congr_fun (hdB v) (dB' v b)
    have e2 := BialgHom.congr_fun (hdB' v) b
    simp only [BialgHom.comp_apply] at e1 e2
    change ψ v (dB v (dB' v b)) = ψ v b
    rw [← e1, ← e2]
    simp
  have h2 : ∀ v, (dB' v).comp (dB v) = BialgHom.id Rh (ℬ.level v) := by
    intro v
    refine BialgHom.ext fun b => hinj v ?_
    have e1 := BialgHom.congr_fun (hdB' v) (dB v b)
    have e2 := BialgHom.congr_fun (hdB v) b
    simp only [BialgHom.comp_apply] at e1 e2
    change ψ v (dB' v (dB v b)) = ψ v b
    rw [← e1, ← e2]
    simp
  refine ⟨uB, fun v => BialgEquiv.ofBialgHom (dB v) (dB' v) (h1 v) (h2 v), huB, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [BialgEquiv.coe_ofBialgHom]
    exact hdB v
  ·
    refine BialgHom.ext fun b => hinj v ?_
    change ψ v (ℬ.transition v (uB (v + 1) b)) = ψ v (uB v (ℬ.transition v b))
    have t1 := BialgHom.congr_fun (hψt v) (uB (v + 1) b)
    have t2 := BialgHom.congr_fun (huB (v + 1)) b
    have t3 := BialgHom.congr_fun (hut v) (ψ (v + 1) b)
    have t4 := BialgHom.congr_fun (hψt v) b
    have t5 := BialgHom.congr_fun (huB v) (ℬ.transition v b)
    simp only [BialgHom.comp_apply] at t1 t2 t3 t4 t5
    rw [← t1, ← t2, t3, t4, t5]
  · refine BialgHom.ext fun b => hinj v ?_
    rw [BialgEquiv.coe_ofBialgHom, BialgEquiv.coe_ofBialgHom]
    change ψ v (ℬ.transition v (dB (v + 1) b)) = ψ v (dB v (ℬ.transition v b))
    have t1 := BialgHom.congr_fun (hψt v) (dB (v + 1) b)
    have t2 := BialgHom.congr_fun (hdB (v + 1)) b
    have t3 := BialgHom.congr_fun (hDpt v) (ψ (v + 1) b)
    have t4 := BialgHom.congr_fun (hψt v) b
    have t5 := BialgHom.congr_fun (hdB v) (ℬ.transition v b)
    simp only [BialgHom.comp_apply] at t1 t2 t3 t4 t5
    rw [← t1, ← t2, t3, t4, t5]

end QB

set_option linter.unusedVariables false in
open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (S : Set ℕ) (d : (ZMod M)ˣ)

    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (heinj : Function.Injective e)
    (herange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))
    (hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x))
    (hsat : ∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e)
    (hcoker : Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])))
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    {hB : ℕ}
    (ℬ : PDivisibleGroup Rh p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

    (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hut : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (u v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)
    (Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v)
    (hDpt : ∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
      (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v))
    (hDpι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ (O.hecke S (CohCarrier.Gen.dia d)).1)

    (hutor : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) →
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp (u v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) ∈ O.toricPts (p ^ v))
    (hDptor : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) →
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) ∈ O.toricPts (p ^ v))

    (hjB : ∀ v, Function.Injective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ψ v)))
    :
    ∃ (uB : ∀ v : ℕ, ℬ.level v →ₐc[Rh] ℬ.level v) (DB : ∀ v : ℕ, ℬ.level v ≃ₐc[Rh] ℬ.level v),
      (∀ v : ℕ, (u v).comp (ψ v) = (ψ v).comp (uB v)) ∧
      (∀ v : ℕ, (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (ψ v) = (ψ v).comp (DB v : ℬ.level v →ₐc[Rh] ℬ.level v)) ∧
      (∀ v : ℕ, (ℬ.transition v).comp (uB (v + 1)) = (uB v).comp (ℬ.transition v)) ∧
      (∀ v : ℕ, (ℬ.transition v).comp (DB (v + 1) : ℬ.level (v + 1) →ₐc[Rh] ℬ.level (v + 1)) =
        (DB v : ℬ.level v →ₐc[Rh] ℬ.level v).comp (ℬ.transition v)) := by
  classical
  exact QB.assemble 𝒢 ℬ ψ
    (fun v => {x | Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v)})
    hψt (fun v x => hψker v x) (fun v b => hψsurj v b) u hut Dp hDpt
    (fun v x hx => hutor v x hx) (fun v x hx => hDptor v x hx) hjB
    (fun v => (QB.eval_baseChange_injective_and_surjective p 𝒢 v).1)
    (fun v => (QB.eval_baseChange_injective_and_surjective p ℬ v).2)
    (fun v f hf => QB.exists_retraction_of_injective_baseChange Rh (ZMod p)
      (ZMod.ringHom_surjective (algebraMap Rh (ZMod p))) f hf)
    (fun v => (PDivisibleGroup.finite_point_and_natCard_point_eq_pow p 𝒢 (AlgebraicClosure ℚ) v).1)

end S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness
end P2MW
export P2MW.S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness (solution)

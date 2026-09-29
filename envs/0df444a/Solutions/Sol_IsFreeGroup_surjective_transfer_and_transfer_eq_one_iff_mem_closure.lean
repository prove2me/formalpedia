-- Prove2me | solution 1 for IsFreeGroup.surjective_transfer_and_transfer_eq_one_iff_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a2d1755a-b8d8-585f-aa77-d5b2999d31be

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FreeCoresSol

open MulAction Subgroup

attribute [local instance] arrowAction arrowMulDistribMulAction

section General

variable {F : Type*} [Group F] {R : Subgroup F} {A : Type*} [CommGroup A]

abbrev V (R : Subgroup F) (A : Type*) : Type _ := F ⧸ R → A

omit [CommGroup A] in
theorem smul_apply' (g : F) (f : V R A) (q : F ⧸ R) : (g • f) q = f (g⁻¹ • q) := rfl

theorem smul_coe_eq_of_mem [R.Normal] {h : F} (hh : h ∈ R) (x : F) :
    h • ((x : F) : F ⧸ R) = (x : F ⧸ R) := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
  have : (h * x)⁻¹ * x = x⁻¹ * h⁻¹ * x⁻¹⁻¹ := by group
  rw [this]
  exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem hh) _

theorem smul_quot_eq_of_mem [R.Normal] {h : F} (hh : h ∈ R) (q : F ⧸ R) : h • q = q := by
  induction q using QuotientGroup.induction_on with
  | H x => exact smul_coe_eq_of_mem hh x

omit [CommGroup A] in

theorem smul_eq_of_mem [R.Normal] {h : F} (hh : h ∈ R) (f : V R A) : h • f = f := by
  funext q
  rw [smul_apply', smul_quot_eq_of_mem (inv_mem hh)]

def IsDer (D : F → V R A) : Prop := ∀ g h : F, D (g * h) = D g * g • D h

namespace IsDer

variable {D E : F → V R A}

theorem map_one (hD : IsDer D) : D 1 = 1 := by
  have h := hD 1 1
  rw [one_mul, one_smul] at h
  exact mul_eq_left.mp h.symm

theorem map_inv (hD : IsDer D) (g : F) : D g⁻¹ = (g⁻¹ • D g)⁻¹ := by
  have h := hD g⁻¹ g
  rw [inv_mul_cancel, hD.map_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem one : IsDer (1 : F → V R A) := fun g h => by
  rw [Pi.one_apply, Pi.one_apply, Pi.one_apply, smul_one, mul_one]

theorem mul (hD : IsDer D) (hE : IsDer E) : IsDer (D * E) := fun g h => by
  simp only [Pi.mul_apply, hD g h, hE g h, smul_mul', mul_mul_mul_comm]

theorem inv (hD : IsDer D) : IsDer D⁻¹ := fun g h => by
  simp only [Pi.inv_apply, hD g h, smul_inv', mul_inv]

theorem div (hD : IsDer D) (hE : IsDer E) : IsDer (D / E) := by
  rw [div_eq_mul_inv]; exact hD.mul hE.inv

theorem prod {ι : Type*} (s : Finset ι) (f : ι → F → V R A) (hf : ∀ i ∈ s, IsDer (f i)) :
    IsDer (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem smul [R.Normal] (hR : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ R) (hD : IsDer D) (a : F) :
    IsDer (fun g => a • D g) := fun g h => by
  show a • D (g * h) = a • D g * g • a • D h
  rw [hD g h, smul_mul', ← mul_smul, ← mul_smul]
  congr 1
  have hmem : (g * a)⁻¹ * (a * g) ∈ R := by
    have := hR a⁻¹ g⁻¹
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
  calc (a * g) • D h = ((g * a) * ((g * a)⁻¹ * (a * g))) • D h := by
          rw [mul_inv_cancel_left]
    _ = (g * a) • D h := by rw [mul_smul, smul_eq_of_mem hmem]

theorem conj [R.Normal] (hD : IsDer D) {h : F} (hh : h ∈ R) (a : F) :
    D (a * h * a⁻¹) = a • D h := by
  rw [hD, hD, hD.map_inv, smul_inv', ← mul_smul,
    smul_eq_of_mem (Subgroup.Normal.conj_mem inferInstance h hh a), mul_inv_eq_iff_eq_mul,
    mul_comm]

end IsDer

def resHom [R.Normal] (D : F → V R A) (hD : IsDer D) : ↥R →* A where
  toFun h := D h ((1 : F) : F ⧸ R)
  map_one' := by rw [OneMemClass.coe_one, hD.map_one]; rfl
  map_mul' h k := by
    rw [Subgroup.coe_mul, hD, Pi.mul_apply, smul_apply',
      smul_quot_eq_of_mem (inv_mem h.2)]

@[scoped simp] theorem resHom_apply [R.Normal] (D : F → V R A) (hD : IsDer D) (h : ↥R) :
    resHom D hD h = D h ((1 : F) : F ⧸ R) := rfl

theorem resHom_conj [R.Normal] (D : F → V R A) (hD : IsDer D) (a : F) (h : ↥R) :
    resHom D hD (MulAut.conjNormal a h) = (a • D h) ((1 : F) : F ⧸ R) := by
  rw [resHom_apply, MulAut.conjNormal_apply, hD.conj h.2]

section Finite

variable [R.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def total (f : V R A) : A := ∏ q, f q

theorem total_mul (f f' : V R A) : total (f * f') = total f * total f' :=
  Finset.prod_mul_distrib

theorem total_smul (g : F) (f : V R A) : total (g • f) = total f := by
  unfold total
  exact Fintype.prod_equiv (MulAction.toPerm g⁻¹) (fun q => (g • f) q) f fun _ => rfl

theorem total_one : total (1 : V R A) = 1 := by simp [total]

noncomputable def totalHom (D : F → V R A) (hD : IsDer D) : F →* A where
  toFun g := total (D g)
  map_one' := by rw [hD.map_one, total_one]
  map_mul' g h := by rw [hD, total_mul, total_smul]

@[scoped simp] theorem totalHom_apply (D : F → V R A) (hD : IsDer D) (g : F) :
    totalHom D hD g = ∏ q, D g q := rfl

end Finite

open scoped Classical in

noncomputable def sec (R : Subgroup F) (q : F ⧸ R) : F :=
  if q = ((1 : F) : F ⧸ R) then 1 else Quotient.out q

theorem sec_spec (q : F ⧸ R) : ((sec R q : F) : F ⧸ R) = q := by
  unfold sec
  split_ifs with h
  · exact h.symm
  · exact QuotientGroup.out_eq' q

theorem sec_one : sec R ((1 : F) : F ⧸ R) = 1 := by
  simp [sec]

theorem sec_mem (g : F) (q : F ⧸ R) : (sec R q)⁻¹ * (g * sec R (g⁻¹ • q)) ∈ R := by
  rw [← QuotientGroup.eq, sec_spec, ← smul_eq_mul, ← MulAction.Quotient.smul_coe, sec_spec,
    smul_inv_smul]

noncomputable def shapiroDer (χ : ↥R →* A) : F → V R A := fun g q => χ ⟨_, sec_mem g q⟩

theorem shapiroDer_apply (χ : ↥R →* A) (g : F) (q : F ⧸ R) :
    shapiroDer χ g q = χ ⟨(sec R q)⁻¹ * (g * sec R (g⁻¹ • q)), sec_mem g q⟩ := rfl

theorem isDer_shapiroDer (χ : ↥R →* A) : IsDer (shapiroDer χ) := by
  intro g h
  funext q
  rw [Pi.mul_apply, smul_apply', shapiroDer_apply, shapiroDer_apply, shapiroDer_apply, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

theorem resHom_shapiroDer [R.Normal] (χ : ↥R →* A) :
    resHom (shapiroDer χ) (isDer_shapiroDer χ) = χ := by
  ext h
  rw [resHom_apply, shapiroDer_apply]
  congr 1
  apply Subtype.ext
  simp only
  rw [smul_coe_eq_of_mem (inv_mem h.2), sec_one, inv_one, one_mul, mul_one]

section Finite

variable [R.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem transfer_eq_prod (χ : ↥R →* A) (g : F) :
    MonoidHom.transfer χ g = ∏ q, shapiroDer χ g q := by
  let T : R.LeftTransversal := ⟨Set.range (sec R), Subgroup.isComplement_range_left sec_spec⟩
  have hT : ∀ q, ((T.2.leftQuotientEquiv q : ↥(T.1)) : F) = sec R q :=
    Subgroup.IsComplement.leftQuotientEquiv_apply sec_spec
  rw [MonoidHom.transfer_def χ T g]
  simp only [Subgroup.leftTransversals.diff]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [shapiroDer_apply]
  congr 1
  apply Subtype.ext
  simp only
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, hT, hT, smul_eq_mul]

theorem transfer_resHom [R.Normal] (D : F → V R A) (hD : IsDer D) (g : F) :
    MonoidHom.transfer (resHom D hD) g = ∏ q, D g q := by
  rw [transfer_eq_prod]
  have key : ∀ q : F ⧸ R, shapiroDer (resHom D hD) g q =
      (D (sec R q) q)⁻¹ * (D g q * D (sec R (g⁻¹ • q)) (g⁻¹ • q)) := by
    intro q
    rw [shapiroDer_apply, resHom_apply, hD, hD.map_inv, Pi.mul_apply, Pi.inv_apply, smul_apply',
      smul_apply', inv_inv, hD, Pi.mul_apply, smul_apply', MulAction.Quotient.smul_coe,
      smul_eq_mul, mul_one, sec_spec]
  simp_rw [key, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [Fintype.prod_equiv (MulAction.toPerm g⁻¹) (fun q => D (sec R (g⁻¹ • q)) (g⁻¹ • q))
    (fun q => D (sec R q) q) fun _ => rfl]
  rw [mul_comm, mul_inv_cancel_right]

theorem transfer_comp_conj [R.Normal] (hR : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ R)
    (χ : ↥R →* A) (a : F) :
    MonoidHom.transfer (χ.comp (MulAut.conjNormal a : MulAut ↥R).toMonoidHom) =
      MonoidHom.transfer χ := by
  have hconj : χ.comp (MulAut.conjNormal a : MulAut ↥R).toMonoidHom =
      resHom (fun g => a • shapiroDer χ g) ((isDer_shapiroDer χ).smul hR a) := by
    ext h
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, resHom_apply]
    conv_lhs => rw [← resHom_shapiroDer (R := R) χ]
    rw [resHom_conj]
  rw [hconj]
  ext g
  rw [transfer_resHom]
  conv_rhs => rw [← resHom_shapiroDer (R := R) χ, transfer_resHom]
  exact Fintype.prod_equiv (MulAction.toPerm a⁻¹) _ _ fun _ => rfl

end Finite

section Free

variable [IsFreeGroup F]

noncomputable abbrev actV (R : Subgroup F) (A : Type*) [CommGroup A] : F →* MulAut (V R A) :=
  mulAutArrow

omit [IsFreeGroup F] in
theorem actV_apply (g : F) (f : V R A) : actV R A g f = g • f := rfl

noncomputable def secOfDer (D : F → V R A) (hD : IsDer D) : F →* (V R A) ⋊[actV R A] F where
  toFun g := ⟨D g, g⟩
  map_one' := by
    ext
    · simp only [hD.map_one, SemidirectProduct.one_left]
    · simp only [SemidirectProduct.one_right]
  map_mul' g h := by
    ext
    · simp only [SemidirectProduct.mul_left, actV_apply, hD g h]
    · simp only [SemidirectProduct.mul_right]

theorem isDer_ext {D E : F → V R A} (hD : IsDer D) (hE : IsDer E)
    (h : ∀ i, D (IsFreeGroup.of i) = E (IsFreeGroup.of i)) : D = E := by
  have key : secOfDer D hD = secOfDer E hE := by
    apply IsFreeGroup.ext_hom
    intro i
    ext
    · exact congrFun (h i) _
    · rfl
  funext g
  exact congrArg SemidirectProduct.left (DFunLike.congr_fun key g)

theorem exists_isDer_apply_of (v : IsFreeGroup.Generators F → V R A) :
    ∃ D : F → V R A, IsDer D ∧ ∀ i, D (IsFreeGroup.of i) = v i := by
  let s : F →* (V R A) ⋊[actV R A] F := IsFreeGroup.lift fun i => ⟨v i, IsFreeGroup.of i⟩
  have hs : ∀ g, (s g).right = g := by
    have hcomp : SemidirectProduct.rightHom.comp s = MonoidHom.id F := by
      apply IsFreeGroup.ext_hom
      intro i
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      simp only [s, IsFreeGroup.lift_of, SemidirectProduct.rightHom_eq_right]
    intro g
    have := DFunLike.congr_fun hcomp g
    simpa using this
  refine ⟨fun g => (s g).left, fun g h => ?_, fun i => ?_⟩
  · show (s (g * h)).left = (s g).left * g • (s h).left
    rw [map_mul, SemidirectProduct.mul_left, hs, actV_apply]
  · show (s (IsFreeGroup.of i)).left = v i
    simp only [s, IsFreeGroup.lift_of]

end Free

section Main

variable [R.Normal] [R.FiniteIndex] [IsFreeGroup F]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem surjective_transfer :
    Function.Surjective (fun χ : ↥R →* A => MonoidHom.transfer χ) := by
  classical
  intro ψ
  obtain ⟨D, hD, hDof⟩ := exists_isDer_apply_of (R := R)
    (fun i => Pi.mulSingle (((1 : F)) : F ⧸ R) (ψ (IsFreeGroup.of i)))
  refine ⟨resHom D hD, ?_⟩
  apply IsFreeGroup.ext_hom
  intro i
  show MonoidHom.transfer (resHom D hD) (IsFreeGroup.of i) = ψ (IsFreeGroup.of i)
  rw [transfer_resHom, hDof]
  exact Finset.prod_pi_mulSingle' _ _ _ |>.trans (if_pos (Finset.mem_univ _))

theorem sec_smul_mulSingle [DecidableEq (F ⧸ R)] (s : F ⧸ R) (a : A) :
    sec R s • (Pi.mulSingle ((1 : F) : F ⧸ R) a : V R A) = Pi.mulSingle s a := by
  funext q
  rw [smul_apply']
  by_cases hq : q = s
  · subst hq
    rw [Pi.mulSingle_eq_same]
    have : (sec R q)⁻¹ • q = ((1 : F) : F ⧸ R) := by
      nth_rewrite 2 [← sec_spec (R := R) q]
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel]
    rw [this, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hq]
    apply Pi.mulSingle_eq_of_ne
    intro h
    apply hq
    have := congrArg (fun x => sec R s • x) h
    simp only [smul_inv_smul, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, sec_spec] at this
    exact this

noncomputable def transferHom (R : Subgroup F) [R.FiniteIndex] (A : Type*) [CommGroup A] :
    (↥R →* A) →* (F →* A) where
  toFun χ := MonoidHom.transfer χ
  map_one' := by
    ext g
    rw [transfer_eq_prod, MonoidHom.one_apply]
    exact Finset.prod_eq_one fun q _ => rfl
  map_mul' χ₁ χ₂ := by
    ext g
    rw [MonoidHom.mul_apply, transfer_eq_prod, transfer_eq_prod, transfer_eq_prod,
      ← Finset.prod_mul_distrib]
    rfl

theorem transfer_eq_one_iff (hR : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ R) (χ : ↥R →* A) :
    MonoidHom.transfer χ = 1 ↔
      χ ∈ Subgroup.closure {ψ : ↥R →* A | ∃ (g : F) (χ' : ↥R →* A),
        ψ = (χ'.comp (MulAut.conjNormal g : MulAut ↥R).toMonoidHom) / χ'} := by
  classical
  constructor
  · intro hχ
    have hD : IsDer (shapiroDer χ) := isDer_shapiroDer χ
    have hDtot : ∀ i, ∏ q, shapiroDer χ (IsFreeGroup.of i) q = 1 := fun i => by
      rw [← transfer_eq_prod, hχ, MonoidHom.one_apply]
    choose Ds hDs hDsof using fun s : F ⧸ R =>
      exists_isDer_apply_of (R := R) (A := A)
        (fun i => Pi.mulSingle ((1 : F) : F ⧸ R) (shapiroDer χ (IsFreeGroup.of i) s))

    let D' : F → V R A := ∏ s : F ⧸ R, ((fun g => sec R s • Ds s g) / Ds s)
    have hD' : IsDer D' :=
      IsDer.prod _ _ fun s _ => ((hDs s).smul hR (sec R s)).div (hDs s)
    have hDD' : shapiroDer χ = D' := by
      refine isDer_ext hD hD' fun i => ?_
      show shapiroDer χ (IsFreeGroup.of i) =
        (∏ s : F ⧸ R, ((fun g => sec R s • Ds s g) / Ds s)) (IsFreeGroup.of i)
      rw [Finset.prod_apply]
      simp only [Pi.div_apply, hDsof, sec_smul_mulSingle]
      have hprod : ∏ s, (Pi.mulSingle ((1 : F) : F ⧸ R) (shapiroDer χ (IsFreeGroup.of i) s) :
          V R A) = Pi.mulSingle ((1 : F) : F ⧸ R) (∏ s, shapiroDer χ (IsFreeGroup.of i) s) :=
        (map_prod (MonoidHom.mulSingle (fun _ : F ⧸ R => A) ((1 : F) : F ⧸ R)) _ _).symm
      rw [Finset.prod_div_distrib, Finset.univ_prod_mulSingle (shapiroDer χ (IsFreeGroup.of i)),
        hprod, hDtot i, Pi.mulSingle_one, div_one]

    have hχeq : χ = ∏ s : F ⧸ R,
        ((resHom (Ds s) (hDs s)).comp (MulAut.conjNormal (sec R s) : MulAut ↥R).toMonoidHom /
          resHom (Ds s) (hDs s)) := by
      ext h
      conv_lhs => rw [← resHom_shapiroDer (R := R) χ, resHom_apply, hDD']
      show (∏ s : F ⧸ R, ((fun g => sec R s • Ds s g) / Ds s)) (h : F) ((1 : F) : F ⧸ R) = _
      rw [MonoidHom.finsetProd_apply, Finset.prod_apply, Finset.prod_apply]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [MonoidHom.div_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, resHom_conj,
        resHom_apply, Pi.div_apply, Pi.div_apply]
    rw [hχeq]
    exact Subgroup.prod_mem _ fun s _ =>
      Subgroup.subset_closure ⟨sec R s, resHom (Ds s) (hDs s), rfl⟩
  · intro hχ
    have hle : Subgroup.closure {ψ : ↥R →* A | ∃ (g : F) (χ' : ↥R →* A),
        ψ = (χ'.comp (MulAut.conjNormal g : MulAut ↥R).toMonoidHom) / χ'} ≤
        (transferHom R A).ker := by
      rw [Subgroup.closure_le]
      rintro ψ ⟨g, χ', rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_div]
      show MonoidHom.transfer _ / MonoidHom.transfer χ' = 1
      rw [transfer_comp_conj hR, div_self']
    exact hle hχ

end Main

end General

end FreeCoresSol
p2m_reactivate "P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure.FreeCoresSol"

theorem solution
    {F : Type*} [Group F] [IsFreeGroup F] (R : Subgroup F) [R.Normal] [R.FiniteIndex]
    (hR : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ R) (A : Type*) [CommGroup A] :
    Function.Surjective (fun χ : ↥R →* A => MonoidHom.transfer χ) ∧
    ∀ χ : ↥R →* A, MonoidHom.transfer χ = 1 ↔
      χ ∈ Subgroup.closure {ψ : ↥R →* A | ∃ (g : F) (χ' : ↥R →* A),
        ψ = (χ'.comp (MulAut.conjNormal g : MulAut ↥R).toMonoidHom) / χ'} :=
  ⟨FreeCoresSol.surjective_transfer, FreeCoresSol.transfer_eq_one_iff hR⟩

end S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure
end P2MW
export P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure (solution)

-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f8020d25-b013-5052-b9ed-c3d0c13cf3fb

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
import Theorems.Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
import Theorems.Thm_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const
import Theorems.Thm_ModularCurve_characterLattice_free_and_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP ModularCurve.CharacterLattice

attribute [local instance 2000] ValuationSubring.instAlgebraSubtypeMem

noncomputable section

namespace ToricReadAsm

section conv

variable {S : Type} [CommRing S] {L : Type} [CommRing L] [Algebra S L] {G : Type} [AddMonoid G]

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) :
    (c * c') (AddMonoidAlgebra.single v 1) =
      c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G) :
    (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) (n : ℕ) :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, convMul_apply_single, ih, pow_succ]

theorem conv_ext {c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)}
    (h : ∀ v, c (AddMonoidAlgebra.single v 1) = c' (AddMonoidAlgebra.single v 1)) : c = c' := by
  have : c.ofConv = c'.ofConv := AddMonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)
  exact congrArg WithConv.toConv this

theorem convPow_eq_one (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (n : ℕ) (hn : ∀ v : G, n • v = 0) :
    c ^ n = 1 := by
  refine conv_ext (fun v => ?_)
  rw [convPow_apply_single, convOne_apply_single, ← map_pow, AddMonoidAlgebra.single_pow, hn, one_pow]
  exact map_one c.ofConv

theorem apply_single_pow_eq_one (c : AddMonoidAlgebra S G →ₐ[S] L) (n : ℕ) (hn : ∀ v : G, n • v = 0) (v : G) :
    c (AddMonoidAlgebra.single v 1) ^ n = 1 := by
  rw [← map_pow, AddMonoidAlgebra.single_pow, hn, one_pow, ← AddMonoidAlgebra.one_def, map_one]

end conv

section eval

variable {S : Type*} [Fintype S] {G : Type*} [CommGroup G]

def evalAt (w : S → G) : Multiplicative (characterLattice S) →* G where
  toFun a := evalHom a.toAdd w
  map_one' := by
    change evalHom (0 : characterLattice S) w = 1
    rw [evalHom_apply]; simp
  map_mul' a b := by
    change evalHom (a.toAdd + b.toAdd) w = _
    exact evalHom_add _ _ w

@[scoped simp] theorem evalAt_apply (w : S → G) (a : Multiplicative (characterLattice S)) :
    evalAt w a = evalHom a.toAdd w := rfl

theorem evalHom_mul (a : characterLattice S) (w w' : S → G) :
    evalHom a (w * w') = evalHom a w * evalHom a w' :=
  (evalHom a).map_mul w w'

theorem evalHom_pow (a : characterLattice S) (w : S → G) (n : ℕ) : evalHom a (w ^ n) = evalHom a w ^ n :=
  (evalHom a).map_pow w n

theorem evalHom_toMul_eq_of_sub_const (a : characterLattice S) (w w' : S → Additive G) (c : G)
    (h : w - w' = fun _ => Additive.ofMul c) :
    evalHom a (fun s => Additive.toMul (w s)) = evalHom a (fun s => Additive.toMul (w' s)) := by
  have hw : (fun s => Additive.toMul (w s)) = (fun s => Additive.toMul (w' s)) * fun _ => c := by
    funext s
    have := congrFun h s
    simp only [Pi.sub_apply] at this
    change Additive.toMul (w s) = Additive.toMul (w' s) * c
    rw [← toMul_ofMul c, ← this, toMul_sub, mul_div_cancel]
  rw [hw, evalHom_mul, evalHom_const, mul_one]

end eval

section core

variable {S : Type*} [Fintype S]
variable {Gκ : Type*} [CommGroup Gκ] {GQ : Type*} [CommGroup GQ] {m : ℕ} (hm : 0 < m)
variable (Tμ : Subgroup Gκ) (hTμ : ∀ g : Gκ, g ∈ Tμ ↔ g ^ m = 1) {TQ : Subgroup GQ}
variable (lift : ↥Tμ →* ↥TQ) (hlift : Function.Injective lift)
variable {Cm : Type*} [Monoid Cm] (htors : ∀ c : Cm, c ^ m = 1)
variable (Pin : Cm → (S → Additive Gκ) → Prop) (R : Cm → (S → Additive Gκ))
variable (hconst : ∀ c wb wb', Pin c wb → Pin c wb' → ∃ c₀ : Gκ, wb - wb' = fun _ => Additive.ofMul c₀)
  (hR : ∀ c, Pin c (R c))
  (hmul : ∀ c c' wb wb', Pin c wb → Pin c' wb' → Pin (c * c') (wb + wb'))

include hconst in
theorem core_eval_eq_of_pin {c : Cm} {wb wb' : S → Additive Gκ} (h : Pin c wb) (h' : Pin c wb')
    (a : characterLattice S) :
    evalHom a (fun s => Additive.toMul (wb s)) = evalHom a (fun s => Additive.toMul (wb' s)) := by
  obtain ⟨c₀, hc⟩ := hconst c wb wb' h h'
  exact evalHom_toMul_eq_of_sub_const a wb wb' c₀ hc

include hconst hR hmul in

theorem core_R_one_const : ∃ c₁ : Gκ, R 1 = fun _ => Additive.ofMul c₁ := by
  have h := hmul 1 1 _ _ (hR 1) (hR 1)
  rw [mul_one] at h
  obtain ⟨c₁, hc⟩ := hconst _ _ _ h (hR 1)
  refine ⟨c₁, ?_⟩
  rw [← hc, add_sub_cancel_right]

include hR hmul in
theorem core_pin_pow (c : Cm) : ∀ n : ℕ, Pin (c ^ (n + 1)) ((n + 1) • R c) := by
  intro n
  induction n with
  | zero => simpa using hR c
  | succ n ih =>
      have := hmul (c ^ (n + 1)) c _ _ ih (hR c)
      rw [← pow_succ] at this
      rwa [succ_nsmul]

include hm htors hconst hR hmul in
theorem core_evalHom_R_pow_m (c : Cm) (a : characterLattice S) :
    evalHom a (fun s => Additive.toMul (R c s)) ^ m = 1 := by
  have hpow := core_pin_pow Pin R hR hmul c (m - 1)
  rw [Nat.sub_add_cancel hm, htors] at hpow
  obtain ⟨c₂, hc₂⟩ := hconst _ _ _ hpow (hR 1)
  obtain ⟨c₁, hc₁⟩ := core_R_one_const Pin R hconst hR hmul
  have hfun : (fun s => Additive.toMul (R c s)) ^ m = fun _ => c₂ * c₁ := by
    funext s
    have h2 := congrFun hc₂ s
    have h1 := congrFun hc₁ s
    simp only [Pi.sub_apply, Pi.smul_apply] at h2 h1
    change Additive.toMul (R c s) ^ m = c₂ * c₁
    rw [← toMul_nsmul, ← sub_add_cancel (m • R c s) (R 1 s), h2, h1]
    rfl
  rw [← evalHom_pow, hfun, evalHom_const]

def coreEvμ (c : Cm) : Multiplicative (characterLattice S) →* ↥Tμ :=
  MonoidHom.codRestrict (evalAt (fun s => Additive.toMul (R c s))) Tμ
    (fun a => (hTμ _).mpr (core_evalHom_R_pow_m hm htors Pin R hconst hR hmul c a.toAdd))

theorem coe_coreEvμ (c : Cm) (a : Multiplicative (characterLattice S)) :
    ((coreEvμ hm Tμ hTμ htors Pin R hconst hR hmul c a : ↥Tμ) : Gκ) =
      evalHom a.toAdd (fun s => Additive.toMul (R c s)) :=
  rfl

def coreE (c : Cm) : characterLattice S →+ Additive ↥TQ :=
  MonoidHom.toAdditiveRight (lift.comp (coreEvμ hm Tμ hTμ htors Pin R hconst hR hmul c))

theorem coreE_apply (c : Cm) (a : characterLattice S) :
    coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c a =
      Additive.ofMul (lift (coreEvμ hm Tμ hTμ htors Pin R hconst hR hmul c (Multiplicative.ofAdd a))) := rfl

theorem coreE_value (c : Cm) (a : characterLattice S) :
    ∃ y : ↥Tμ, Additive.toMul (coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c a) = lift y ∧
      (y : Gκ) = evalHom a (fun s => Additive.toMul (R c s)) :=
  ⟨coreEvμ hm Tμ hTμ htors Pin R hconst hR hmul c (Multiplicative.ofAdd a), rfl, rfl⟩

include hlift in
theorem coreE_apply_eq_iff (c c' : Cm) (a a' : characterLattice S) :
    coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c a = coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c' a' ↔
      evalHom a (fun s => Additive.toMul (R c s)) = evalHom a' (fun s => Additive.toMul (R c' s)) := by
  rw [coreE_apply, coreE_apply]
  constructor
  · intro h
    have h1 := hlift (Additive.ofMul.injective h)
    have h2 := congrArg (fun y : ↥Tμ => (y : Gκ)) h1
    simpa only [coe_coreEvμ, toAdd_ofAdd] using h2
  · intro h
    congr 2
    exact Subtype.ext h

include hlift in
theorem coreE_mul (c c' : Cm) :
    coreE hm Tμ hTμ lift htors Pin R hconst hR hmul (c * c') =
      coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c + coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c' := by
  refine AddMonoidHom.ext fun a => ?_
  rw [AddMonoidHom.add_apply]
  have hev := core_eval_eq_of_pin Pin hconst (hR (c * c')) (hmul c c' _ _ (hR c) (hR c')) a
  have hev' : evalHom a (fun s => Additive.toMul (R (c * c') s)) =
      evalHom a (fun s => Additive.toMul (R c s)) * evalHom a (fun s => Additive.toMul (R c' s)) := by
    rw [← evalHom_mul]; exact hev
  rw [coreE_apply, coreE_apply, coreE_apply, ← ofMul_mul, ← map_mul]
  congr 2
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  exact hev'

include hlift in
theorem coreE_one : coreE hm Tμ hTμ lift htors Pin R hconst hR hmul 1 = 0 := by
  have h := coreE_mul hm Tμ hTμ lift hlift htors Pin R hconst hR hmul 1 1
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

def coreEhom : Cm →* Multiplicative (characterLattice S →+ Additive ↥TQ) :=
  { toFun := fun c => Multiplicative.ofAdd (coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c)
    map_one' := congrArg Multiplicative.ofAdd (coreE_one hm Tμ hTμ lift hlift htors Pin R hconst hR hmul)
    map_mul' := fun c c' =>
      congrArg Multiplicative.ofAdd (coreE_mul hm Tμ hTμ lift hlift htors Pin R hconst hR hmul c c') }

include hlift in

theorem core_eval_eq_one_of_coreE_eq_zero (c : Cm) (h : coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c = 0)
    (a : characterLattice S) : evalHom a (fun s => Additive.toMul (R c s)) = 1 := by
  have h1 := DFunLike.congr_fun h a
  rw [AddMonoidHom.zero_apply, coreE_apply] at h1
  have h2 : lift (coreEvμ hm Tμ hTμ htors Pin R hconst hR hmul c (Multiplicative.ofAdd a)) = 1 :=
    Additive.ofMul.injective h1
  rw [← map_one lift] at h2
  have h3 := congrArg (fun y : ↥Tμ => (y : Gκ)) (hlift h2)
  first | (simpa only [toAdd_ofAdd] using h3) | (simpa only [toAdd_ofAdd, OneMemClass.coe_one] using h3) | (simp only [toAdd_ofAdd, OneMemClass.coe_one] at h3 ⊢; exact h3)

def coreEOn {T : Type*} [AddCommGroup T] (Φ : Cm ≃* Multiplicative T) :
    T →+ (characterLattice S →+ Additive ↥TQ) :=
  AddMonoidHom.toMultiplicative.symm
    ((coreEhom hm Tμ hTμ lift hlift htors Pin R hconst hR hmul).comp Φ.symm.toMonoidHom)

theorem coreEOn_apply {T : Type*} [AddCommGroup T] (Φ : Cm ≃* Multiplicative T) (c : Cm) :
    coreEOn hm Tμ hTμ lift hlift htors Pin R hconst hR hmul Φ (Φ c).toAdd =
      coreE hm Tμ hTμ lift htors Pin R hconst hR hmul c :=
  congrArg (fun z => (coreEhom hm Tμ hTμ lift hlift htors Pin R hconst hR hmul z).toAdd) (Φ.symm_apply_apply c)

include hlift in

theorem coreEOn_injective {T : Type*} [AddCommGroup T] (Φ : Cm ≃* Multiplicative T)
    (h1 : ∀ c : Cm, (∀ a : characterLattice S, evalHom a (fun s => Additive.toMul (R c s)) = 1) → c = 1) :
    Function.Injective (coreEOn hm Tμ hTμ lift hlift htors Pin R hconst hR hmul Φ) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨c, rfl⟩ : ∃ c, x = (Φ c).toAdd := ⟨Φ.symm (Multiplicative.ofAdd x), by simp⟩
  rw [coreEOn_apply] at hx
  have hc := h1 c (core_eval_eq_one_of_coreE_eq_zero hm Tμ hTμ lift hlift htors Pin R hconst hR hmul c hx)
  rw [hc, map_one]
  rfl

end core

theorem castOver_comp {B T X : Scheme.{0}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') (z : SchemeHomOver ι f)
    (φ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp (castOver h z) φ = castOver h (NeronModelInfra.schemeHomOverComp z φ) := by
  subst h; rfl

theorem comp_transport_aux {X Y Z W : Scheme.{0}} (S' : X ⟶ Y) (S : X ⟶ Y) (ρ : Y ⟶ Y) (ι : Y ⟶ Z)
    (F : Z ⟶ Z) (fst : Z ⟶ W) (fst' : Z ⟶ W) (φ1 : W ⟶ W) (P P' : X ⟶ W)
    (hS : S' = S ≫ ρ) (hψ1 : ρ ≫ ι = ι ≫ F) (hF : F ≫ fst' = fst ≫ φ1) (h : S ≫ ι ≫ fst = P)
    (hφ1 : P' = P ≫ φ1) : S' ≫ ι ≫ fst' = P' := by
  subst hS hφ1
  rw [← h]
  simp only [Category.assoc]
  rw [← Category.assoc ρ ι fst', hψ1, Category.assoc, hF]

section lift

variable {A : ValuationSubring (AlgebraicClosure ℚ)} (m : ℕ) [NeZero m]
variable (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
  (h2surj : ∀ u : (ResidueField ↥A), u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)

abbrev θ : rootsOfUnity m ↥A →* rootsOfUnity m (ResidueField ↥A) := restrictRootsOfUnity (residue ↥A) m

theorem coe_pow_eq_one {Rg : Type*} [CommMonoid Rg] (ζ : rootsOfUnity m Rg) : ((ζ : Rgˣ) : Rg) ^ m = 1 := by
  rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ζ.2, Units.val_one]

include h2inj in
theorem θ_injective : Function.Injective (θ (A := A) m) := by
  intro ζ ζ' h
  have hv := congrArg (fun y : rootsOfUnity m (ResidueField ↥A) => ((y : (ResidueField ↥A)ˣ) : (ResidueField ↥A))) h
  simp only [restrictRootsOfUnity_coe_apply] at hv
  have e := h2inj _ _ (coe_pow_eq_one m ζ) (coe_pow_eq_one m ζ') hv
  exact Subtype.ext (Units.ext e)

include h2surj in
theorem θ_surjective : Function.Surjective (θ (A := A) m) := by
  intro y
  obtain ⟨ζ, hζ, hres⟩ := h2surj _ (coe_pow_eq_one m y)
  refine ⟨rootsOfUnity.mkOfPowEq ζ hζ, Subtype.ext (Units.ext ?_)⟩
  rw [restrictRootsOfUnity_coe_apply, rootsOfUnity.val_mkOfPowEq_coe, hres]

def θE : rootsOfUnity m ↥A ≃* rootsOfUnity m (ResidueField ↥A) :=
  MulEquiv.ofBijective (θ m) ⟨θ_injective m h2inj, θ_surjective m h2surj⟩

theorem θ_θE_symm (y : rootsOfUnity m (ResidueField ↥A)) : θ m ((θE m h2inj h2surj).symm y) = y :=
  (θE m h2inj h2surj).apply_symm_apply y

theorem residue_θE_symm (y : rootsOfUnity m (ResidueField ↥A)) :
    residue ↥A ((((θE m h2inj h2surj).symm y : rootsOfUnity m ↥A) : (↥A)ˣ) : ↥A) = ((y : (ResidueField ↥A)ˣ) : (ResidueField ↥A)) := by
  have := congrArg (fun z : rootsOfUnity m (ResidueField ↥A) => ((z : (ResidueField ↥A)ˣ) : (ResidueField ↥A))) (θ_θE_symm m h2inj h2surj y)
  simpa only [restrictRootsOfUnity_coe_apply] using this

abbrev ιQ : rootsOfUnity m ↥A →* rootsOfUnity m (AlgebraicClosure ℚ) := restrictRootsOfUnity (algebraMap ↥A (AlgebraicClosure ℚ)) m

theorem ιQ_injective : Function.Injective (ιQ (A := A) m) := by
  intro ζ ζ' h
  have hv := congrArg (fun y : rootsOfUnity m (AlgebraicClosure ℚ) => ((y : (AlgebraicClosure ℚ)ˣ) : (AlgebraicClosure ℚ))) h
  simp only [restrictRootsOfUnity_coe_apply] at hv
  exact Subtype.ext (Units.ext (Subtype.val_injective hv))

def liftμ : rootsOfUnity m (ResidueField ↥A) →* rootsOfUnity m (AlgebraicClosure ℚ) := (ιQ m).comp (θE m h2inj h2surj).symm.toMonoidHom

theorem liftμ_injective : Function.Injective (liftμ m h2inj h2surj) :=
  (ιQ_injective m).comp (θE m h2inj h2surj).symm.injective

theorem coe_liftμ (y : rootsOfUnity m (ResidueField ↥A)) :
    ((liftμ m h2inj h2surj y : (AlgebraicClosure ℚ)ˣ) : (AlgebraicClosure ℚ)) = ((((θE m h2inj h2surj).symm y : rootsOfUnity m ↥A) : (↥A)ˣ) : ↥A) :=
  restrictRootsOfUnity_coe_apply _ _

end lift

section main

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
  {m : ℕ} (hm : 0 < m)

abbrev AChar (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) : Type := muCoord ↥A O.toricRank m →ₐ[↥A] ↥A

abbrev NodeDatum (O : JHNeronObjectAtP p M H hpM A hA Λ) : Type := ↥O.ssFinset → Additive (ResidueField ↥A)ˣ

abbrev SPm (χ : AChar O m) : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ O.G :=
  Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
    pullback.fst O.g Λ.σA

abbrev Pin (χ : AChar O m) (wb : NodeDatum O) : Prop :=
  SPm O hm χ = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1

abbrev PinC (c : WithConv (AChar O m)) (wb : NodeDatum O) : Prop := Pin O hm c.ofConv wb

theorem nodeUnit_eq_of_pin (c : WithConv (AChar O m)) (wb wb' : NodeDatum O) (h : PinC O hm c wb)
    (h' : PinC O hm c wb') : GluedPic0.nodeUnit O.ssFinset wb = GluedPic0.nodeUnit O.ssFinset wb' :=
  O.ptsSp.injective (Subtype.ext (h.symm.trans h'))

theorem pin_const
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 → ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (c : WithConv (AChar O m)) (wb wb' : NodeDatum O) (h : PinC O hm c wb) (h' : PinC O hm c wb') :
    ∃ c₀ : (ResidueField ↥A)ˣ, wb - wb' = fun _ => Additive.ofMul c₀ := by
  refine hker _ ?_
  rw [map_sub, nodeUnit_eq_of_pin O hm c wb wb' h h', sub_self]

theorem convPow_m_eq_one [NeZero m] (c : WithConv (AChar O m)) : c ^ m = 1 :=
  convPow_eq_one c m (fun v => by funext i; simp)

abbrev liftQ (χ : AChar O m) : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ := (Algebra.ofId ↥A _).comp χ

theorem liftQ_injective : Function.Injective (liftQ O (m := m)) := by
  intro χ χ' h
  refine AlgHom.ext fun x => Subtype.val_injective ?_
  exact congrArg (fun f : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ => f x) h

theorem liftQ_convMul (c c' : WithConv (AChar O m)) :
    liftQ O (c * c').ofConv = (WithConv.toConv (liftQ O c.ofConv) * WithConv.toConv (liftQ O c'.ofConv)).ofConv :=
  AlgHom.comp_convMul_distrib (Algebra.ofId ↥A (AlgebraicClosure ℚ)) c c'

theorem eq_one_of_eval_trivial [NeZero m] [Nonempty ↥O.ssFinset]
    (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (htriv4 : ∀ (χ : AChar O m) (wb : NodeDatum O), Pin O hm χ wb → GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∀ v : Fin O.toricRank → ZMod m, IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single v 1)) = 1)
    (hquot : ∀ w : ↥O.ssFinset → (ResidueField ↥A)ˣ,
      (∀ a : characterLattice ↥O.ssFinset, evalHom a w = 1) ↔ ∃ c : (ResidueField ↥A)ˣ, w = fun _ => c)
    (c : WithConv (AChar O m)) (hev : ∀ a : characterLattice ↥O.ssFinset, evalHom a (fun s => Additive.toMul (R c s)) = 1) :
    c = 1 := by
  obtain ⟨c₀, hc₀⟩ := (hquot _).mp hev
  have hconst : R c = fun _ => Additive.ofMul c₀ := by
    funext s
    apply Additive.toMul.injective
    simpa using congrFun hc₀ s
  have h0 : GluedPic0.nodeUnit O.ssFinset (R c) = 0 := by
    rw [hconst]; exact GluedPic0.nodeUnit_const O.ssFinset c₀
  have htr := htriv4 c.ofConv (R c) (hR c) h0
  have hc1 : ∀ v, c.ofConv (AddMonoidAlgebra.single v 1) = 1 := fun v =>
    h2inj _ _ (apply_single_pow_eq_one c.ofConv m (fun v => by funext i; simp) v) (one_pow m)
      (by rw [map_one]; exact htr v)
  exact conv_ext fun v => by rw [hc1 v, convOne_apply_single]

section Phi

def g₁ (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x) :
    WithConv (AChar O m) →* Multiplicative ↥(O.toricPts m) where
  toFun c := Multiplicative.ofAdd ⟨O.toricPoint m hm (liftQ O c.ofConv), (hmem1 _).mpr ⟨_, rfl⟩⟩
  map_one' := by
    have h : O.toricPoint m hm (liftQ O (1 * 1 : WithConv (AChar O m)).ofConv) =
        O.toricPoint m hm (liftQ O (1 : WithConv (AChar O m)).ofConv) +
          O.toricPoint m hm (liftQ O (1 : WithConv (AChar O m)).ofConv) := by
      rw [liftQ_convMul, hmul1]
    rw [mul_one] at h
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext (add_eq_left.mp h.symm)
  map_mul' c c' := by
    rw [← ofAdd_add]
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    change O.toricPoint m hm (liftQ O (c * c').ofConv) =
      O.toricPoint m hm (liftQ O c.ofConv) + O.toricPoint m hm (liftQ O c'.ofConv)
    rw [liftQ_convMul, hmul1]

variable (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x)

theorem coe_g₁ (c : WithConv (AChar O m)) :
    (((g₁ O hm hmul1 hmem1 c).toAdd : ↥(O.toricPts m)) : JH M H) = O.toricPoint m hm (liftQ O c.ofConv) := rfl

theorem g₁_injective (hinj1 : Function.Injective (O.toricPoint m hm)) : Function.Injective (g₁ O hm hmul1 hmem1) := by
  intro c c' h
  have h1 := congrArg (fun z : Multiplicative ↥(O.toricPts m) => ((z.toAdd : ↥(O.toricPts m)) : JH M H)) h
  simp only [coe_g₁] at h1
  exact WithConv.ofConv_injective (liftQ_injective O (hinj1 h1))

theorem g₁_surjective (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x) : Function.Surjective (g₁ O hm hmul1 hmem1) := by
  intro z
  obtain ⟨χ, hχ⟩ := (hmem1 _).mp z.toAdd.2
  obtain ⟨χA, hχA⟩ := hAval χ
  refine ⟨WithConv.toConv χA, ?_⟩
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  change O.toricPoint m hm (liftQ O χA) = (z.toAdd : JH M H)
  rw [← hχ]
  congr 1
  exact AlgHom.ext hχA

def Φ (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x) : WithConv (AChar O m) ≃* Multiplicative ↥(O.toricPts m) :=
  MulEquiv.ofBijective (g₁ O hm hmul1 hmem1) ⟨g₁_injective O hm hmul1 hmem1 hinj1, g₁_surjective O hm hmul1 hmem1 hAval⟩

theorem Φ_apply (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x) (c : WithConv (AChar O m)) :
    Φ O hm hmul1 hmem1 hinj1 hAval c = g₁ O hm hmul1 hmem1 c := rfl

theorem exists_eq_g₁ (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x) (x : ↥(O.toricPts m)) :
    ∃ c : WithConv (AChar O m), x = (g₁ O hm hmul1 hmem1 c).toAdd :=
  ⟨(Φ O hm hmul1 hmem1 hinj1 hAval).symm (Multiplicative.ofAdd x),
    (congrArg Multiplicative.toAdd ((Φ O hm hmul1 hmem1 hinj1 hAval).apply_symm_apply (Multiplicative.ofAdd x))).symm⟩

end Phi

section transport

variable (ψ : SchemeHomOver (muStr ↥A O.toricRank m) (muStr ↥A O.toricRank m))

def ρA : muCoord ↥A O.toricRank m →ₐ[↥A] muCoord ↥A O.toricRank m :=
  { (Spec.preimage ψ.1).hom with
    commutes' := fun c => by
      have hcomp : CommRingCat.ofHom (algebraMap ↥A (muCoord ↥A O.toricRank m)) ≫ Spec.preimage ψ.1 =
          CommRingCat.ofHom (algebraMap ↥A (muCoord ↥A O.toricRank m)) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact ψ.2
      have := congrArg (fun g => (CommRingCat.Hom.hom g) c) hcomp
      simpa using this }

theorem spec_ρA : Spec.map (CommRingCat.ofHom (ρA O ψ).toRingHom) = ψ.1 := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage ψ.1).hom) = ψ.1
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem muPt_comp (χ : AChar O m) :
    NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (liftQ O χ)) ψ =
      muPt A O.toricRank m (liftQ O (χ.comp (ρA O ψ))) := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe]
  change Spec.map (CommRingCat.ofHom (liftQ O χ).toRingHom) ≫ ψ.1 =
    Spec.map (CommRingCat.ofHom (liftQ O (χ.comp (ρA O ψ))).toRingHom)
  rw [← spec_ρA O ψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (φ : SchemeHomOver O.g O.g)
  (hψ : NeronModelInfra.schemeHomOverComp ψ (O.toricLift m hm) =
    NeronModelInfra.schemeHomOverComp (O.toricLift m hm) (fibreRestrictAlong Λ.σA O.g O.g φ))
include hψ

theorem act_toricPoint (χ : AChar O m) :
    O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (O.toricPoint m hm (liftQ O χ))) φ) =
      O.toricPoint m hm (liftQ O (χ.comp (ρA O ψ))) := by
  unfold JHNeronObjectAtP.toricPoint
  rw [Equiv.apply_symm_apply]
  congr 1
  unfold genOfBaseChangePt
  rw [castOver_comp, ← RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    NeronModelInfra.schemeHomOverComp_assoc, ← hψ, ← NeronModelInfra.schemeHomOverComp_assoc, muPt_comp]

theorem pin_transport (op : NodeDatum O → NodeDatum O)
    (hφ : ∀ w : NodeDatum O,
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) φ) =
        GluedPic0.nodeUnit O.ssFinset (op w))
    (χ : AChar O m) (wb : NodeDatum O) (h : Pin O hm χ wb) : Pin O hm (χ.comp (ρA O ψ)) (op wb) := by
  have hψ1 : ψ.1 ≫ (O.toricLift m hm).1 = (O.toricLift m hm).1 ≫ (fibreRestrictAlong Λ.σA O.g O.g φ).1 := by
    have := congrArg Subtype.val hψ
    simpa only [NeronModelInfra.schemeHomOverComp_coe] using this
  have hφ1 : (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (op wb))).1 =
      (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 ≫ φ.1 := by
    rw [← hφ wb, Equiv.apply_symm_apply, NeronModelInfra.schemeHomOverComp_coe]
  have hS : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (χ.comp (ρA O ψ)).toRingHom)) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ ψ.1 := by
    rw [← spec_ρA O ψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact comp_transport_aux _ _ ψ.1 (O.toricLift m hm).1 (fibreRestrictAlong Λ.σA O.g O.g φ).1
    (pullback.fst O.g Λ.σA) (pullback.fst O.g Λ.σA) φ.1 _ _ hS hψ1
    (fibreRestrictAlong_coe_comp_fst Λ.σA O.g O.g φ) h hφ1

end transport

section clauses

variable [NeZero m]

abbrev EC (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c) :
    WithConv (AChar O m) → (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))) :=
  coreE hm (rootsOfUnity m (ResidueField ↥A)) (fun g => mem_rootsOfUnity m g) (liftμ m h2inj h2surj)
    (convPow_m_eq_one O) (PinC O hm) R (pin_const O hm hker) hR hmul4

abbrev eH (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x)
    (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x) :
    ↥(O.toricPts m) →+ (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))) :=
  coreEOn hm (rootsOfUnity m (ResidueField ↥A)) (fun g => mem_rootsOfUnity m g) (liftμ m h2inj h2surj)
    (liftμ_injective m h2inj h2surj) (convPow_m_eq_one O) (PinC O hm) R (pin_const O hm hker) hR hmul4
    (Φ O hm hmul1 hmem1 hinj1 hAval)

theorem eH_g₁ (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x)
    (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x) (c : WithConv (AChar O m)) :
    eH O hm h2inj h2surj R hR hmul4 hker hmul1 hmem1 hinj1 hAval (g₁ O hm hmul1 hmem1 c).toAdd =
      EC O hm h2inj h2surj R hR hmul4 hker c :=
  coreEOn_apply hm (rootsOfUnity m (ResidueField ↥A)) (fun g => mem_rootsOfUnity m g) (liftμ m h2inj h2surj)
    (liftμ_injective m h2inj h2surj) (convPow_m_eq_one O) (PinC O hm) R (pin_const O hm hker) hR hmul4
    (Φ O hm hmul1 hmem1 hinj1 hAval) c

theorem clause1 (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x)
    (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x)
    (e : ↥(O.toricPts m) → (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))))
    (he : ∀ c, e (g₁ O hm hmul1 hmem1 c).toAdd = EC O hm h2inj h2surj R hR hmul4 hker c)
    (χ : AChar O m) (wb : NodeDatum O) (hpin : Pin O hm χ wb) :
    ∃ hx : O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ) ∈ O.toricPts m,
      ∀ a : characterLattice ↥O.ssFinset, ∃ u : ↥A,
        (u : AlgebraicClosure ℚ) = (((Additive.toMul (e ⟨_, hx⟩ a) : ↥(rootsOfUnity m (AlgebraicClosure ℚ))) :
          (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∧
        IsLocalRing.residue ↥A u = ((evalHom a (fun s => Additive.toMul (wb s)) : (ResidueField ↥A)ˣ) : ResidueField ↥A) := by
  refine ⟨(hmem1 _).mpr ⟨_, rfl⟩, fun a => ?_⟩

  have hval : e ⟨O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ), (hmem1 _).mpr ⟨_, rfl⟩⟩ =
      EC O hm h2inj h2surj R hR hmul4 hker (WithConv.toConv χ) := he (WithConv.toConv χ)
  obtain ⟨y, hy1, hy2⟩ := coreE_value hm (rootsOfUnity m (ResidueField ↥A)) (fun g => mem_rootsOfUnity m g)
    (liftμ m h2inj h2surj) (convPow_m_eq_one O) (PinC O hm) R (pin_const O hm hker) hR hmul4 (WithConv.toConv χ) a
  have h1 : Additive.toMul (e ⟨O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ),
      (hmem1 _).mpr ⟨_, rfl⟩⟩ a) = liftμ m h2inj h2surj y :=
    (congrArg (fun F : characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ)) =>
      Additive.toMul (F a)) hval).trans hy1
  refine ⟨((((θE m h2inj h2surj).symm y : rootsOfUnity m ↥A) : (↥A)ˣ) : ↥A), ?_, ?_⟩
  · exact ((coe_liftμ m h2inj h2surj y).symm).trans
      (congrArg (fun v : ↥(rootsOfUnity m (AlgebraicClosure ℚ)) => ((v : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h1).symm
  · rw [residue_θE_symm, hy2]
    exact congrArg Units.val (core_eval_eq_of_pin (PinC O hm) (pin_const O hm hker) (hR (WithConv.toConv χ)) hpin a)

theorem EC_transport (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (f : characterLattice ↥O.ssFinset →ₗ[ℤ] characterLattice ↥O.ssFinset)
    (op : (↥O.ssFinset → Additive (ResidueField ↥A)ˣ) →+ (↥O.ssFinset → Additive (ResidueField ↥A)ˣ))
    (hadj : ∀ (a : characterLattice ↥O.ssFinset) (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
      evalHom (f a) (fun s => Additive.toMul (w s)) = evalHom a (fun s => Additive.toMul (op w s)))
    (c c' : WithConv (AChar O m)) (hpin' : PinC O hm c' (op (R c))) :
    EC O hm h2inj h2surj R hR hmul4 hker c' = (EC O hm h2inj h2surj R hR hmul4 hker c).comp f.toAddMonoidHom := by
  refine AddMonoidHom.ext fun a => ?_
  refine (coreE_apply_eq_iff hm (rootsOfUnity m (ResidueField ↥A)) (fun g => mem_rootsOfUnity m g)
    (liftμ m h2inj h2surj) (liftμ_injective m h2inj h2surj) (convPow_m_eq_one O) (PinC O hm) R (pin_const O hm hker)
    hR hmul4 c' c a (f a)).mpr ?_
  rw [core_eval_eq_of_pin (PinC O hm) (pin_const O hm hker) (hR c') hpin' a]
  exact (hadj a (R c)).symm

theorem clause2 (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x)
    (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x)
    (e : ↥(O.toricPts m) → (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))))
    (he : ∀ c, e (g₁ O hm hmul1 hmem1 c).toAdd = EC O hm h2inj h2surj R hR hmul4 hker c)
    (φ : SchemeHomOver O.g O.g)
    (f : characterLattice ↥O.ssFinset →ₗ[ℤ] characterLattice ↥O.ssFinset)
    (op : (↥O.ssFinset → Additive (ResidueField ↥A)ˣ) →+ (↥O.ssFinset → Additive (ResidueField ↥A)ˣ))
    (hadj : ∀ (a : characterLattice ↥O.ssFinset) (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
      evalHom (f a) (fun s => Additive.toMul (w s)) = evalHom a (fun s => Additive.toMul (op w s)))
    (hφ : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) φ) =
        GluedPic0.nodeUnit O.ssFinset (op w))
    (ψ : SchemeHomOver (muStr ↥A O.toricRank m) (muStr ↥A O.toricRank m))
    (hψ : NeronModelInfra.schemeHomOverComp ψ (O.toricLift m hm) =
      NeronModelInfra.schemeHomOverComp (O.toricLift m hm) (fibreRestrictAlong Λ.σA O.g O.g φ))
    (x : ↥(O.toricPts m)) :
    ∃ hx : O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (x : JH M H)) φ) ∈ O.toricPts m,
      e ⟨_, hx⟩ = (e x).comp f.toAddMonoidHom := by
  obtain ⟨c, rfl⟩ := exists_eq_g₁ O hm hmul1 hmem1 hinj1 hAval x
  have hact := act_toricPoint O hm ψ φ hψ c.ofConv

  have e1 := congrArg (fun z : JH M H => O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts z) φ))
    (coe_g₁ O hm hmul1 hmem1 c)
  have e2 : O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts ((g₁ O hm hmul1 hmem1 c).toAdd).1) φ) =
      ((g₁ O hm hmul1 hmem1 (WithConv.toConv (c.ofConv.comp (ρA O ψ)))).toAdd).1 :=
    (e1.trans hact).trans (coe_g₁ O hm hmul1 hmem1 (WithConv.toConv (c.ofConv.comp (ρA O ψ)))).symm
  have hmem : O.pts.symm (NeronModelInfra.schemeHomOverComp
      (O.pts ((g₁ O hm hmul1 hmem1 c).toAdd).1) φ) ∈ O.toricPts m :=
    (hmem1 _).mpr ⟨liftQ O (c.ofConv.comp (ρA O ψ)), (e1.trans hact).symm⟩
  refine ⟨hmem, ?_⟩
  have hxg : (⟨O.pts.symm (NeronModelInfra.schemeHomOverComp
      (O.pts ((g₁ O hm hmul1 hmem1 c).toAdd).1) φ), hmem⟩ : ↥(O.toricPts m)) =
      (g₁ O hm hmul1 hmem1 (WithConv.toConv (c.ofConv.comp (ρA O ψ)))).toAdd :=
    Subtype.ext e2

  have key := EC_transport O hm h2inj h2surj R hR hmul4 hker f op hadj c (WithConv.toConv (c.ofConv.comp (ρA O ψ)))
    (pin_transport O hm ψ φ hψ op hφ c.ofConv (R c) (hR c))
  exact ((congrArg e hxg).trans (he _)).trans
    (key.trans (congrArg (fun F : characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ)) =>
      F.comp f.toAddMonoidHom) (he c)).symm)

theorem eH_injective [Nonempty ↥O.ssFinset] (h2inj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂)
    (h2surj : ∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u)
    (R : WithConv (AChar O m) → NodeDatum O) (hR : ∀ c, PinC O hm c (R c))
    (hmul4 : ∀ (c c' : WithConv (AChar O m)) (wb wb' : NodeDatum O),
      PinC O hm c wb → PinC O hm c' wb' → PinC O hm (c * c') (wb + wb'))
    (hker : ∀ wb : NodeDatum O, GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c)
    (hmul1 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint m hm (χ * χ').ofConv = O.toricPoint m hm χ.ofConv + O.toricPoint m hm χ'.ofConv)
    (hmem1 : ∀ x : JH M H, x ∈ O.toricPts m ↔ ∃ χ, O.toricPoint m hm χ = x)
    (hinj1 : Function.Injective (O.toricPoint m hm))
    (hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x)
    (htriv4 : ∀ (χ : AChar O m) (wb : NodeDatum O), Pin O hm χ wb → GluedPic0.nodeUnit O.ssFinset wb = 0 →
      ∀ v : Fin O.toricRank → ZMod m, IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single v 1)) = 1)
    (hquot : ∀ w : ↥O.ssFinset → (ResidueField ↥A)ˣ,
      (∀ a : characterLattice ↥O.ssFinset, evalHom a w = 1) ↔ ∃ c : (ResidueField ↥A)ˣ, w = fun _ => c) :
    Function.Injective (eH O hm h2inj h2surj R hR hmul4 hker hmul1 hmem1 hinj1 hAval) :=
  coreEOn_injective hm (rootsOfUnity m (ResidueField ↥A)) (fun g => mem_rootsOfUnity m g) (liftμ m h2inj h2surj)
    (liftμ_injective m h2inj h2surj) (convPow_m_eq_one O) (PinC O hm) R (pin_const O hm hker) hR hmul4
    (Φ O hm hmul1 hmem1 hinj1 hAval) (eq_one_of_eval_trivial O hm h2inj R hR htriv4 hquot)

end clauses

theorem natCard_addMonoidHom_eq {Lt : Type*} [AddCommGroup Lt] [Module.Free ℤ Lt] [Module.Finite ℤ Lt]
    {Mμ : Type*} [AddCommGroup Mμ] [Finite Mμ] :
    Nat.card (Lt →+ Mμ) = Nat.card Mμ ^ Module.finrank ℤ Lt := by
  classical
  let b := Module.finBasis ℤ Lt
  have e : (Lt →+ Mμ) ≃ (Fin (Module.finrank ℤ Lt) → Mμ) :=
    (addMonoidHomLequivInt (A := Lt) (B := Mμ) ℤ).toEquiv.trans (b.constr ℤ).symm.toEquiv
  rw [Nat.card_congr e]
  haveI := Fintype.ofFinite Mμ
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]

end main

end ToricReadAsm
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit.ToricReadAsm"

end
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit.ToricReadAsm"

open ToricReadAsm in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) (hmp : m.Coprime p)
    (hker : ∀ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      GluedPic0.nodeUnit O.ssFinset wb = 0 → ∃ c : (ResidueField ↥A)ˣ, wb = fun _ => Additive.ofMul c) :
    ∃ e : ↥(O.toricPts m) ≃+ (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))),

      (∀ (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        ∃ hx : O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ) ∈ O.toricPts m,
          ∀ a : characterLattice ↥O.ssFinset, ∃ u : ↥A,
            (u : AlgebraicClosure ℚ) = (((Additive.toMul (e ⟨_, hx⟩ a) : ↥(rootsOfUnity m (AlgebraicClosure ℚ))) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∧
            IsLocalRing.residue ↥A u = ((evalHom a (fun s => Additive.toMul (wb s)) : (ResidueField ↥A)ˣ) : ResidueField ↥A)) ∧

      (∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A, ∃ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1) ∧

      (∀ (φ : SchemeHomOver O.g O.g)
        (hφmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
          NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
            O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
        (f : characterLattice ↥O.ssFinset →ₗ[ℤ] characterLattice ↥O.ssFinset)
        (op : (↥O.ssFinset → Additive (ResidueField ↥A)ˣ) →+ (↥O.ssFinset → Additive (ResidueField ↥A)ˣ))
        (hadj : ∀ (a : characterLattice ↥O.ssFinset) (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
          evalHom (f a) (fun s => Additive.toMul (w s)) = evalHom a (fun s => Additive.toMul (op w s)))
        (hφ : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) φ) =
            GluedPic0.nodeUnit O.ssFinset (op w))
        (hφtor : ∃ ψ : SchemeHomOver (muStr ↥A O.toricRank m) (muStr ↥A O.toricRank m),
          NeronModelInfra.schemeHomOverComp ψ (O.toricLift m hm) =
            NeronModelInfra.schemeHomOverComp (O.toricLift m hm) (fibreRestrictAlong Λ.σA O.g O.g φ)),
        ∀ x : ↥(O.toricPts m),
          ∃ hx : O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts (x : JH M H)) φ) ∈ O.toricPts m,
            e ⟨_, hx⟩ = (e x).comp f.toAddMonoidHom) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩

  have H1 := ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
      p M H hpM A hA Λ O m hm
  have hmul1 := H1.1
  have hinj1 := H1.2.1
  have hmem1 := H1.2.2.1
  have hcard1 := H1.2.2.2

  have hmκ : (m : ResidueField ↥A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ResidueField ↥A) p m]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hmp.symm
  have H2 := ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed (AlgebraicClosure ℚ) A m hmκ
  have h2inj := H2.1
  have h2surj := H2.2

  have H4 := ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one p M H hpM A hA Λ O m hm
  have hmul4 := H4.2.1
  have htriv4 := H4.2.2
  let R0 : AChar O m → NodeDatum O := fun χ => (H4.1 χ).choose
  have hR0 : ∀ χ, Pin O hm χ (R0 χ) := fun χ => (H4.1 χ).choose_spec

  have hAval : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, ∃ χA : AChar O m,
      ∀ x, (χA x : AlgebraicClosure ℚ) = χ x := fun χ =>
    (ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder A
      (fun g => isOfFinAddOrder_of_finite g) χ).2
  haveI : Nonempty ↥O.ssFinset := by
    rw [← Fintype.card_pos_iff, Fintype.card_coe, ← O.toricRank_succ_eq_card]
    exact Nat.succ_pos _
  have HQ := ModularCurve.characterLattice_evalHom_surjective_and_trivial_iff_const (↥O.ssFinset) ((ResidueField ↥A)ˣ)
  have hquot := HQ.2

  let eHm := eH O hm h2inj h2surj (fun c => R0 c.ofConv) (fun c => hR0 c.ofConv) hmul4 hker hmul1 hmem1 hinj1 hAval
  have hinj : Function.Injective eHm :=
    eH_injective O hm h2inj h2surj (fun c => R0 c.ofConv) (fun c => hR0 c.ofConv) hmul4 hker hmul1 hmem1 hinj1 hAval
      htriv4 hquot

  have H5 := ModularCurve.characterLattice_free_and_finrank_eq (↥O.ssFinset)
  haveI := H5.1
  have hrank := H5.2
  haveI : Module.Finite ℤ (characterLattice ↥O.ssFinset) :=
    Module.Finite.of_injective (characterLattice ↥O.ssFinset).subtype (Submodule.injective_subtype _)
  have ht : Module.finrank ℤ (characterLattice ↥O.ssFinset) = O.toricRank := by
    rw [hrank, Fintype.card_coe, ← O.toricRank_succ_eq_card, Nat.add_sub_cancel]
  haveI : NeZero (m : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have hζ := (HasEnoughRootsOfUnity.prim (M := AlgebraicClosure ℚ) (n := m)).choose_spec
  have hμ : Nat.card (Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))) = m := by
    change Nat.card ↥(rootsOfUnity m (AlgebraicClosure ℚ)) = m
    first | rw [hζ.card_rootsOfUnity] | rw [Nat.card_eq_fintype_card, hζ.card_rootsOfUnity]
  haveI : Finite (Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))) :=
    Nat.finite_of_card_ne_zero (by rw [hμ]; exact hm.ne')
  have hcardHom : Nat.card (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))) =
      m ^ O.toricRank := by
    rw [natCard_addMonoidHom_eq, hμ, ht]
  haveI : Finite ↥(O.toricPts m) := Nat.finite_of_card_ne_zero (by rw [hcard1]; exact pow_ne_zero _ hm.ne')
  haveI : Finite (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardHom]; exact pow_ne_zero _ hm.ne')
  have hbij : Function.Bijective eHm := by
    letI := Fintype.ofFinite ↥(O.toricPts m)
    letI := Fintype.ofFinite (characterLattice ↥O.ssFinset →+ Additive ↥(rootsOfUnity m (AlgebraicClosure ℚ)))
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard1, hcardHom]
  have he : ∀ c, (AddEquiv.ofBijective eHm hbij) (g₁ O hm hmul1 hmem1 c).toAdd =
      EC O hm h2inj h2surj (fun c => R0 c.ofConv) (fun c => hR0 c.ofConv) hmul4 hker c := fun c =>
    eH_g₁ O hm h2inj h2surj (fun c => R0 c.ofConv) (fun c => hR0 c.ofConv) hmul4 hker hmul1 hmem1 hinj1 hAval c
  exact ⟨AddEquiv.ofBijective eHm hbij,
    fun χ wb hpin => clause1 O hm h2inj h2surj (fun c => R0 c.ofConv) (fun c => hR0 c.ofConv) hmul4 hker hmul1 hmem1
      hinj1 hAval _ he χ wb hpin,
    fun χ => ⟨R0 χ, hR0 χ⟩,
    fun φ hφmul f op hadj hφ hφtor x => clause2 O hm h2inj h2surj (fun c => R0 c.ofConv) (fun c => hR0 c.ofConv) hmul4
      hker hmul1 hmem1 hinj1 hAval _ he φ f op hadj hφ hφtor.choose hφtor.choose_spec x⟩

end S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit (solution)

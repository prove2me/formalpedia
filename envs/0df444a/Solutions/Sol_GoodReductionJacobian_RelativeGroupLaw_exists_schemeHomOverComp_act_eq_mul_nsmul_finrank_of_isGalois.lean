-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b45d10b9-5e42-5378-941d-a13b328d26c3

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois

set_option autoImplicit false

noncomputable section

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_succ nsmul_natural IsCommutative pointGroup one_natural mul_natural mul"
namespace TorsorPhi
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {K : Type u} [Field K] {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of K)}

abbrev pointCommGroup (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) : CommGroup (SchemeHomOver t fA) :=
  { LA.pointGroup t with mul_comm := fun x y => hc t x y }

def bigProd (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} (s : Finset ι) (F : ι → SchemeHomOver t fA) :
    SchemeHomOver t fA :=
  @Finset.prod ι (SchemeHomOver t fA) (pointCommGroup LA hc t).toCommMonoid s F

theorem nsmul_eq_pow (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t fA) :
    LA.nsmul t n x = @HPow.hPow _ ℕ _ (@instHPow _ ℕ (pointCommGroup LA hc t).toMonoid.toPow) x n := by
  letI := pointCommGroup LA hc t
  induction n with
  | zero => rfl
  | succ n ih => rw [LA.nsmul_succ, pow_succ, ih]; rfl

theorem bigProd_natural (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') {ι : Type*} (s : Finset ι) (F : ι → SchemeHomOver t fA) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (bigProd LA hc t s F) =
      bigProd LA hc t' s (fun i => GoodReductionJacobian.schemeHomOverComp ψ hψ (F i)) := by
  letI := pointCommGroup LA hc t
  letI := pointCommGroup LA hc t'
  let φ : SchemeHomOver t fA →* SchemeHomOver t' fA :=
    { toFun := GoodReductionJacobian.schemeHomOverComp ψ hψ
      map_one' := LA.one_natural t t' ψ hψ
      map_mul' := fun x y => LA.mul_natural t t' ψ hψ x y }
  exact map_prod φ F s

theorem bigProd_mul_left (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} [Fintype ι] (a : SchemeHomOver t fA)
    (F : ι → SchemeHomOver t fA) :
    bigProd LA hc t Finset.univ (fun i => LA.mul t a (F i)) =
      LA.mul t (bigProd LA hc t Finset.univ F) (LA.nsmul t (Fintype.card ι) a) := by
  letI := pointCommGroup LA hc t
  rw [nsmul_eq_pow LA hc]
  show (∏ i, a * F i) = (∏ i, F i) * a ^ (Fintype.card ι)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm]

theorem bigProd_equiv (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} [Fintype ι] (e : ι ≃ ι)
    (F G : ι → SchemeHomOver t fA) (h : ∀ i, F i = G (e i)) :
    bigProd LA hc t Finset.univ F = bigProd LA hc t Finset.univ G := by
  letI := pointCommGroup LA hc t
  exact Fintype.prod_equiv e F G h

theorem bigProd_congr (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {ι : Type*} (s : Finset ι)
    (F G : ι → SchemeHomOver t fA) (h : ∀ i, F i = G i) :
    bigProd LA hc t s F = bigProd LA hc t s G := by
  letI := pointCommGroup LA hc t
  exact Finset.prod_congr rfl fun i _ => h i

structure TorsorData (LA : RelativeGroupLaw K fA) {V : Scheme.{u}}
    (g : V ⟶ Spec (CommRingCat.of K)) where

  act : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
    SchemeHomOver t fA → SchemeHomOver t g → SchemeHomOver t g

  act_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t fA) (v : SchemeHomOver t g),
    GoodReductionJacobian.schemeHomOverComp ψ hψ (act t a v) =
      act t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v)

  act_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a b : SchemeHomOver t fA) (v : SchemeHomOver t g),
    act t (LA.mul t a b) v = act t a (act t b v)

  act_torsor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g),
    ∃! a : SchemeHomOver t fA, act t a v = w

namespace TorsorData

variable {LA : RelativeGroupLaw K fA} {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)}
  (D : TorsorData LA g)

def delta {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g) :
    SchemeHomOver t fA :=
  (D.act_torsor t w v).choose

theorem act_delta {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g) :
    D.act t (D.delta t v w) w = v :=
  (D.act_torsor t w v).choose_spec.1

theorem delta_unique {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g)
    (a : SchemeHomOver t fA) (ha : D.act t a w = v) : a = D.delta t v w :=
  (D.act_torsor t w v).unique ha (D.act_delta t v w)

theorem delta_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (v w : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (D.delta t v w) =
      D.delta t' (GoodReductionJacobian.schemeHomOverComp ψ hψ v)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ w) := by
  apply D.delta_unique
  rw [← D.act_natural, D.act_delta]

theorem delta_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
    (v w : SchemeHomOver t g) :
    D.delta t (D.act t a v) w = LA.mul t a (D.delta t v w) := by
  symm
  apply D.delta_unique
  rw [D.act_mul, D.act_delta]

end TorsorData

section Galois

variable (K' : Type u) [Field K'] [Algebra K K']

abbrev baseExt (K : Type u) [Field K] (K' : Type u) [Field K'] [Algebra K K'] :
    Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'))

abbrev specAut {K : Type u} [Field K] {K' : Type u} [Field K'] [Algebra K K'] (σ : K' ≃ₐ[K] K') :
    Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K') :=
  Spec.map (CommRingCat.ofHom ((σ : K' →ₐ[K] K') : K' →+* K'))

theorem specAut_comp_baseExt (σ : K' ≃ₐ[K] K') : specAut σ ≫ baseExt K K' = baseExt K K' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

theorem specAut_mul (σ τ : K' ≃ₐ[K] K') : specAut (τ * σ) = specAut τ ≫ specAut σ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable {K'}
variable {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)}
  (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K')

def conjPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') : SchemeHomOver t g :=
  ⟨t' ≫ specAut σ ≫ P, by rw [Category.assoc, Category.assoc, hP, specAut_comp_baseExt, ht]⟩

@[scoped simp]
theorem conjPt_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') :
    (conjPt P hP t t' ht σ).1 = t' ≫ specAut σ ≫ P := rfl

theorem conjPt_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t₂ : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t₂)
    (t' : T ⟶ Spec (CommRingCat.of K')) (ht : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (conjPt P hP t t' ht σ) =
      conjPt P hP t₂ (ψ ≫ t') (by rw [Category.assoc, ht, hψ]) σ :=
  Subtype.ext (by simp)

theorem conjPt_twist {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T ⟶ Spec (CommRingCat.of K')) (τ : K' ≃ₐ[K] K')
    (ht : (t' ≫ specAut τ) ≫ baseExt K K' = t) (ht' : t' ≫ baseExt K K' = t) (σ : K' ≃ₐ[K] K') :
    conjPt P hP t (t' ≫ specAut τ) ht σ = conjPt P hP t t' ht' (τ * σ) :=
  Subtype.ext (by simp [specAut_mul])

variable (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative) (D : TorsorData LA g)
  [FiniteDimensional K K']

def Psi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (v : SchemeHomOver t g) : SchemeHomOver t fA :=
  bigProd LA hc t Finset.univ (fun σ : K' ≃ₐ[K] K' => D.delta t v (conjPt P hP t t' ht σ))

theorem Psi_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t₂ : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t₂)
    (t' : T ⟶ Spec (CommRingCat.of K')) (ht : t' ≫ baseExt K K' = t) (v : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (Psi P hP LA hc D t t' ht v) =
      Psi P hP LA hc D t₂ (ψ ≫ t') (by rw [Category.assoc, ht, hψ])
        (GoodReductionJacobian.schemeHomOverComp ψ hψ v) := by
  unfold Psi
  rw [bigProd_natural]
  refine bigProd_congr LA hc t₂ _ _ _ fun σ => ?_
  rw [D.delta_natural, conjPt_natural]

theorem Psi_congr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    {t'₁ t'₂ : T ⟶ Spec (CommRingCat.of K')} (e : t'₁ = t'₂)
    (h₁ : t'₁ ≫ baseExt K K' = t) (h₂ : t'₂ ≫ baseExt K K' = t)
    {v₁ v₂ : SchemeHomOver t g} (ev : v₁.1 = v₂.1) :
    Psi P hP LA hc D t t'₁ h₁ v₁ = Psi P hP LA hc D t t'₂ h₂ v₂ := by
  subst e
  cases Subtype.ext ev
  rfl

theorem Psi_twist {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T ⟶ Spec (CommRingCat.of K')) (τ : K' ≃ₐ[K] K')
    (ht : (t' ≫ specAut τ) ≫ baseExt K K' = t) (ht' : t' ≫ baseExt K K' = t) (v : SchemeHomOver t g) :
    Psi P hP LA hc D t (t' ≫ specAut τ) ht v = Psi P hP LA hc D t t' ht' v := by
  unfold Psi
  refine bigProd_equiv LA hc t (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [conjPt_twist P hP t t' τ ht ht']
  rfl

theorem Psi_act {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T ⟶ Spec (CommRingCat.of K')) (ht : t' ≫ baseExt K K' = t)
    (a : SchemeHomOver t fA) (v : SchemeHomOver t g) :
    Psi P hP LA hc D t t' ht (D.act t a v) =
      LA.mul t (Psi P hP LA hc D t t' ht v) (LA.nsmul t (Fintype.card (K' ≃ₐ[K] K')) a) := by
  unfold Psi
  rw [← bigProd_mul_left]
  refine bigProd_congr LA hc t _ _ _ fun σ => ?_
  rw [D.delta_act]

end Galois

section Descent

variable (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
  {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)} (D : TorsorData LA g)
  (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K')

abbrev tV : pullback g (baseExt K K') ⟶ Spec (CommRingCat.of K) :=
  pullback.snd g (baseExt K K') ≫ baseExt K K'

def vpt : SchemeHomOver (tV K' (g := g)) g :=
  ⟨pullback.fst g (baseExt K K'), pullback.condition⟩

def psiPt : SchemeHomOver (tV K' (g := g)) fA :=
  Psi P hP LA hc D (tV K') (pullback.snd g (baseExt K K')) rfl (vpt K')

def fK : pullback g (baseExt K K') ⟶ pullback fA (baseExt K K') :=
  pullback.lift (psiPt K' LA hc D P hP).1 (pullback.snd g (baseExt K K')) (psiPt K' LA hc D P hP).2

@[reassoc]
theorem fK_fst : fK K' LA hc D P hP ≫ pullback.fst fA (baseExt K K') = (psiPt K' LA hc D P hP).1 :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem fK_snd : fK K' LA hc D P hP ≫ pullback.snd fA (baseExt K K') = pullback.snd g (baseExt K K') :=
  pullback.lift_snd _ _ _

theorem comp_psiPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : T ⟶ pullback g (baseExt K K')) (hx : x ≫ tV K' = t) :
    x ≫ (psiPt K' LA hc D P hP).1 =
      (Psi P hP LA hc D t (x ≫ pullback.snd g (baseExt K K')) (by rw [Category.assoc]; exact hx)
        ⟨x ≫ pullback.fst g (baseExt K K'), by
          rw [Category.assoc, pullback.condition]; exact hx⟩).1 := by
  have h := congrArg Subtype.val
    (Psi_natural P hP LA hc D (tV K') t x hx (pullback.snd g (baseExt K K')) rfl (vpt K'))
  exact h

theorem twist_comp_fK (σ : K' ≃ₐ[K] K') (hσ : specAut σ ≫ baseExt K K' = baseExt K K') :
    pullback.map g (baseExt K K') g (baseExt K K') (𝟙 V) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ fK K' LA hc D P hP =
      fK K' LA hc D P hP ≫ pullback.map fA (baseExt K K') fA (baseExt K K') (𝟙 A) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, fK_fst, Category.comp_id]
    have hx : pullback.map g (baseExt K K') g (baseExt K K') (𝟙 V) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ tV K' = tV K' := by
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, hσ]
    rw [comp_psiPt K' LA hc D P hP (tV K') _ hx]
    have e : pullback.map g (baseExt K K') g (baseExt K K') (𝟙 V) (specAut σ) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫
          pullback.snd g (baseExt K K') = pullback.snd g (baseExt K K') ≫ specAut σ :=
      pullback.lift_snd _ _ _
    have hs : (pullback.snd g (baseExt K K') ≫ specAut σ) ≫ baseExt K K' = tV K' := by
      rw [Category.assoc, hσ]
    rw [congrArg Subtype.val (Psi_congr P hP LA hc D (tV K') e _ hs (v₂ := vpt K')
      (by show _ ≫ pullback.fst g (baseExt K K') = pullback.fst g (baseExt K K')
          rw [pullback.lift_fst]; exact Category.comp_id _))]
    exact congrArg Subtype.val (Psi_twist P hP LA hc D (tV K') _ σ hs rfl (vpt K'))
  · simp only [Category.assoc, pullback.lift_snd, fK_snd, fK_snd_assoc]

theorem comp_eq_Psi (φ : V ⟶ A)
    (hφ' : (psiPt K' LA hc D P hP).1 = pullback.fst g (baseExt K K') ≫ φ)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (t' : T ⟶ Spec (CommRingCat.of K'))
    (ht : t' ≫ baseExt K K' = t) (w : SchemeHomOver t g) :
    w.1 ≫ φ = (Psi P hP LA hc D t t' ht w).1 := by
  let x : T ⟶ pullback g (baseExt K K') := pullback.lift w.1 t' (by rw [w.2, ht])
  have hx : x ≫ tV K' = t := by rw [← Category.assoc, pullback.lift_snd, ht]
  calc w.1 ≫ φ = (x ≫ pullback.fst g (baseExt K K')) ≫ φ := by rw [pullback.lift_fst]
    _ = x ≫ (psiPt K' LA hc D P hP).1 := by rw [Category.assoc, ← hφ']
    _ = _ := comp_psiPt K' LA hc D P hP t x hx
    _ = (Psi P hP LA hc D t t' ht w).1 :=
        congrArg Subtype.val (Psi_congr P hP LA hc D t (pullback.lift_snd _ _ _) _ ht
          (pullback.lift_fst _ _ _))

variable [IsGalois K K'] [IsSeparated fA] [LocallyOfFiniteType fA]

theorem exists_descent :
    ∃ (φ : V ⟶ A), φ ≫ fA = g ∧
      (psiPt K' LA hc D P hP).1 = pullback.fst g (baseExt K K') ≫ φ := by
  obtain ⟨φ, hφ, hf, -⟩ :=
    AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq_of_finiteDimensional
      K K' V A g fA (fK K' LA hc D P hP) (fK_snd K' LA hc D P hP)
      (fun σ hσ => twist_comp_fK K' LA hc D P hP σ hσ)
  refine ⟨φ, hφ, ?_⟩
  rw [← fK_fst, hf, pullback.lift_fst]

end Descent

theorem exists_hom (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [IsGalois K K']
    [IsSeparated fA] [LocallyOfFiniteType fA]
    (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
    {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)} (D : TorsorData LA g)
    (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K') :
    ∃ φ : SchemeHomOver g fA,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
        (v : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (D.act t a v) φ =
          LA.mul t (NeronModelInfra.schemeHomOverComp v φ)
            (LA.nsmul t (Module.finrank K K') a) := by
  obtain ⟨φ, hφ, hφ'⟩ := exists_descent K' LA hc D P hP
  refine ⟨⟨φ, hφ⟩, fun {T} t a v => ?_⟩
  have hcard : Fintype.card (K' ≃ₐ[K] K') = Module.finrank K K' := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K K'
  apply Subtype.ext
  simp only [NeronModelInfra.schemeHomOverComp_coe]
  let p := pullback.fst t (baseExt K K')
  let t' := pullback.snd t (baseExt K K')
  have hp : t' ≫ baseExt K K' = p ≫ t := pullback.condition.symm
  rw [← cancel_epi p]

  have eL : p ≫ (D.act t a v).1 ≫ φ =
      (LA.mul (p ≫ t)
        (Psi P hP LA hc D (p ≫ t) t' hp (GoodReductionJacobian.schemeHomOverComp p rfl v))
        (LA.nsmul (p ≫ t) (Fintype.card (K' ≃ₐ[K] K'))
          (GoodReductionJacobian.schemeHomOverComp p rfl a))).1 := by
    have h1 : p ≫ (D.act t a v).1 =
        (D.act (p ≫ t) (GoodReductionJacobian.schemeHomOverComp p rfl a)
          (GoodReductionJacobian.schemeHomOverComp p rfl v)).1 :=
      congrArg Subtype.val (D.act_natural t (p ≫ t) p rfl a v)
    rw [← Category.assoc, h1, comp_eq_Psi K' LA hc D P hP φ hφ' (p ≫ t) t' hp, Psi_act]

  have eR : p ≫ (LA.mul t (NeronModelInfra.schemeHomOverComp v ⟨φ, hφ⟩)
        (LA.nsmul t (Module.finrank K K') a)).1 =
      (LA.mul (p ≫ t)
        (Psi P hP LA hc D (p ≫ t) t' hp (GoodReductionJacobian.schemeHomOverComp p rfl v))
        (LA.nsmul (p ≫ t) (Fintype.card (K' ≃ₐ[K] K'))
          (GoodReductionJacobian.schemeHomOverComp p rfl a))).1 := by
    have h1 := congrArg Subtype.val
      (LA.mul_natural t (p ≫ t) p rfl (NeronModelInfra.schemeHomOverComp v ⟨φ, hφ⟩)
        (LA.nsmul t (Module.finrank K K') a))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
    rw [h1, ← LA.nsmul_natural, hcard]
    have h2 : GoodReductionJacobian.schemeHomOverComp p rfl
        (NeronModelInfra.schemeHomOverComp v ⟨φ, hφ⟩) =
        Psi P hP LA hc D (p ≫ t) t' hp (GoodReductionJacobian.schemeHomOverComp p rfl v) := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
        ← Category.assoc]
      exact comp_eq_Psi K' LA hc D P hP φ hφ' (p ≫ t) t' hp
        (GoodReductionJacobian.schemeHomOverComp p rfl v)
    rw [h2]
  rw [eL, eR]

end GoodReductionJacobian.RelativeGroupLaw.TorsorPhi
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian.RelativeGroupLaw.TorsorPhi"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian"

open _root_.GoodReductionJacobian.RelativeGroupLaw _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian.RelativeGroupLaw in

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (fA : A ⟶ Spec (CommRingCat.of K))
    [IsSeparated fA] [LocallyOfFiniteType fA]
    (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
    {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K))
    (act : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      SchemeHomOver t fA → SchemeHomOver t g → SchemeHomOver t g)
    (act_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (a : SchemeHomOver t fA) (v : SchemeHomOver t g),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (act t a v) =
        act t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
          (GoodReductionJacobian.schemeHomOverComp ψ hψ v))
    (act_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (a b : SchemeHomOver t fA) (v : SchemeHomOver t g),
      act t (LA.mul t a b) v = act t a (act t b v))
    (act_torsor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g),
      ∃! a : SchemeHomOver t fA, act t a v = w)
    (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [IsGalois K K']
    (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K'))) :
    ∃ φ : SchemeHomOver g fA,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
        (v : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (act t a v) φ =
          LA.mul t (NeronModelInfra.schemeHomOverComp v φ) (LA.nsmul t (Module.finrank K K') a) :=
  TorsorPhi.exists_hom K' LA hc ⟨act, act_natural, act_mul, act_torsor⟩ P hP

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.GoodReductionJacobian.RelativeGroupLaw.TorsorPhi"

end S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois (solution)

-- Prove2me | solution 1 for ModularCurve.setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bcbb829d-9bb6-5ac6-b5ad-e4dd28b747e4

import Mathlib
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroup_map_subtype_iff
import Theorems.Thm_ModularCurve_eisensteinNumerator_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

namespace VIAssembly

section Helpers

universe u

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have e := congrArg Subtype.val (L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint)
  rw [hx] at e
  exact e

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f) (h : L.mul t a a = a) :
    a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t a) a := by rw [h]
    _ = L.one t := L.inv_mul_cancel t a

theorem one_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t t' : T ⟶ Spec (CommRingCat.of R)} (he : t = t') : (L.one t).1 = (L.one t').1 := by
  subst he; rfl

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t t' : T ⟶ Spec (CommRingCat.of R)} (he : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst he
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

theorem eq_of_isSeparated_of_generic_eq {K : Type u} [Field K] (O : ValuationSubring K)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (σ : Spec (CommRingCat.of ↥O) ⟶ Y)
    (x y : SchemeHomOver σ f)
    (h : Spec.map (CommRingCat.ofHom O.subtype) ≫ x.1 = Spec.map (CommRingCat.ofHom O.subtype) ≫ y.1) :
    x = y := by
  let S : ValuativeCommSq f :=
    ValuativeCommSq.mk (↥O) K (Spec.map (CommRingCat.ofHom O.subtype) ≫ x.1) σ
      ⟨by rw [Category.assoc, x.2]; rfl⟩
  have hU : ValuativeCriterion.Uniqueness f := IsSeparated.valuativeCriterion f
  have hsub : Subsingleton S.commSq.LiftStruct := hU S
  let l₁ : S.commSq.LiftStruct := ⟨x.1, rfl, x.2⟩
  let l₂ : S.commSq.LiftStruct := ⟨y.1, h.symm, y.2⟩
  haveI := hsub
  have e : l₁ = l₂ := Subsingleton.elim l₁ l₂
  exact Subtype.ext (congrArg CommSq.LiftStruct.l e)

theorem baseChangePointToBase_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).nsmul t' n x) =
      L.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι L t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

theorem schemeNsmul_baseChange_fst (L : RelativeGroupLaw R f) (n : ℕ) :
    (L.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ L.schemeNsmul n := by
  have h1 : (L.baseChange ι).schemeNsmul n ≫ pullback.fst f ι =
      (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).nsmul _ n RelativeGroupLaw.idPoint)).1 := rfl
  rw [h1, baseChangePointToBase_nsmul, ← comp_schemeNsmul]
  rfl

theorem schemeNsmul_baseChange_eq_map (L : RelativeGroupLaw R f) (n : ℕ) :
    (L.baseChange ι).schemeNsmul n =
      pullback.map f ι f ι (L.schemeNsmul n) (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans (L.schemeNsmul_over n).symm) ((Category.comp_id _).trans rfl) := by
  apply pullback.hom_ext
  · rw [schemeNsmul_baseChange_fst, pullback.lift_fst]
  · rw [pullback.lift_snd, Category.comp_id]
    exact (L.baseChange ι).schemeNsmul_over n

end Helpers

theorem isUnit_natCast_of_liesOverPrime {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (k : ℕ) (hk : ¬ p ∣ k) : IsUnit (k : ↥A) := by
  by_contra hku
  have hcop : IsCoprime (k : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_comm).1 ((hp.coprime_iff_not_dvd).2 hk))
  obtain ⟨a, b, hab⟩ := hcop
  have hkm : (k : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := hku
  have hpm : (p : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have h : ((p : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simp at hA ⊢; exact hA
    exact (A.coe_mem_nonunits_iff).1 h
  have h1 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (a : ↥A) hkm) (Ideal.mul_mem_left _ (b : ↥A) hpm)
    have e : ((a : ℤ) : ↥A) * (k : ↥A) + ((b : ℤ) : ↥A) * (p : ↥A) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ↥A) hab |>.trans Int.cast_one
    rwa [e] at this
  exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem mem_inertiaInvariantPoints_of_extends
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g) (hcomm : L.IsCommutative)
    (hlfp : ∀ n : ℕ, 0 < n → LocallyOfFinitePresentation (L.schemeNsmul n))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y))
    (pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (k : ℕ) (hk : ¬ p ∣ k) (x : JZero p) (hx : k • x = 0)
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)
    (hs : (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1) :
    x ∈ inertiaInvariantPoints p A := by
  classical
  have hp : p.Prime := Fact.out
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => hk (h ▸ dvd_zero p))

  have hjι : (Spec.map (CommRingCat.ofHom A.subtype)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp]
    congr 1

  have h1 : pts 0 = L.one _ :=
    eq_one_of_mul_self L _ _ (by have e := pts_add 0 0; rw [add_zero] at e; exact e.symm)
  have hpow : ∀ (c : ℕ) (z : JZero p), pts (c • z) = L.nsmul _ c (pts z) := by
    intro c z
    induction c with
    | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]; exact h1
    | succ c ih => rw [succ_nsmul, pts_add, ih, RelativeGroupLaw.nsmul_succ]

  have hsgen : schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) hjι s = pts x := Subtype.ext hs.symm

  have hks : L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) k s = L.one (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) := by
    apply eq_of_isSeparated_of_generic_eq A g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))
    have e1 : (Spec.map (CommRingCat.ofHom A.subtype)) ≫ (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) k s).1 = (L.nsmul _ k (pts x)).1 := by
      have := congrArg Subtype.val (L.nsmul_natural (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) _ (Spec.map (CommRingCat.ofHom A.subtype)) hjι k s)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      rw [this, hsgen]
    have e2 : (Spec.map (CommRingCat.ofHom A.subtype)) ≫ (L.one (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))).1 =
        (L.one (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).1 := by
      have := congrArg Subtype.val (L.one_natural (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) _ (Spec.map (CommRingCat.ofHom A.subtype)) hjι)
      rwa [GoodReductionJacobian.schemeHomOverComp_coe] at this
    rw [e1, e2, ← hpow, hx, h1]

  intro σ hσ
  have hσ' : σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype := hσ
  obtain ⟨hstab, hred⟩ := (ValuationSubring.mem_inertiaSubgroup_map_subtype_iff A σ).1 hσ'
  let σA : ↥A →+* ↥A :=
    ((σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype).codRestrict A
      (fun a => (hstab a.1).2 a.2)
  have hσA : A.subtype.comp σA = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
    RingHom.ext fun _ => rfl
  set τ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥A) := Spec.map (CommRingCat.ofHom σA) with hτ
  have hτι : τ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) := by
    rw [hτ, ← Spec.map_comp]
    congr 1
    all_goals exact CommRingCat.hom_ext (RingHom.ext_int _ _)
  have hjτ : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (Spec.map (CommRingCat.ofHom A.subtype)) = (Spec.map (CommRingCat.ofHom A.subtype)) ≫ τ := by
    rw [hτ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    all_goals exact CommRingCat.hom_ext hσA.symm
  have hresτ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ τ =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
    rw [hτ, ← Spec.map_comp]
    congr 1
    ext a
    show IsLocalRing.residue ↥A (σA a) = IsLocalRing.residue ↥A a
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (A.coe_mem_nonunits_iff).1 (hred a.1 a.2)

  let L' := L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))
  let s₁ : SchemeHomOver (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) g := ⟨s.1, by rw [Category.id_comp]; exact s.2⟩
  let s₂ : SchemeHomOver (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) g :=
    ⟨τ ≫ s.1, by rw [Category.id_comp, Category.assoc, s.2, hτι]⟩
  have hτι' : τ ≫ (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) = 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) := by rw [Category.id_comp]; exact hτι
  have hs₂ : s₂ = schemeHomOverComp τ hτι' s₁ := Subtype.ext rfl
  have hks₁ : L.nsmul _ k s₁ = L.one _ := by
    have e : s₁ = schemeHomOverComp (𝟙 _) rfl s := Subtype.ext (Category.id_comp _).symm
    calc L.nsmul _ k s₁ = schemeHomOverComp (𝟙 _) rfl (L.nsmul _ k s) := by rw [e, ← L.nsmul_natural]
      _ = schemeHomOverComp (𝟙 _) rfl (L.one _) := by rw [hks]
      _ = L.one _ := L.one_natural _ _ _ _
  have hks₂ : L.nsmul _ k s₂ = L.one _ := by
    calc L.nsmul _ k s₂ = schemeHomOverComp τ hτι' (L.nsmul _ k s₁) := by rw [hs₂, ← L.nsmul_natural]
      _ = schemeHomOverComp τ hτι' (L.one _) := by rw [hks₁]
      _ = L.one _ := L.one_natural _ _ _ _
  let u₁ : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) s₁
  let u₂ : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) s₂
  have hu : ∀ (u : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)),
      L.nsmul _ k (RelativeGroupLaw.baseChangePointToBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) u) = L.one _ →
      u.1 ≫ L'.schemeNsmul k = (L'.one (𝟙 _)).1 := by
    intro u hu
    rw [comp_schemeNsmul]
    congr 1
    have e := baseChangePointToBase_nsmul (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L (𝟙 _) k u
    rw [hu] at e
    rw [← RelativeGroupLaw.baseChangePointOfBase_toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) (L'.nsmul (𝟙 _) k u), e]
    rfl
  have hg' : u₁.1 ≫ L'.schemeNsmul k = u₂.1 ≫ L'.schemeNsmul k := by
    rw [hu u₁ (by rw [RelativeGroupLaw.baseChangePointToBase_ofBase]; exact hks₁),
      hu u₂ (by rw [RelativeGroupLaw.baseChangePointToBase_ofBase]; exact hks₂)]
  have hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1 := by
    apply pullback.hom_ext
    · show Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ pullback.lift s₁.1 (𝟙 _) s₁.2 ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ pullback.lift s₂.1 (𝟙 _) s₂.2 ≫ pullback.fst _ _
      rw [pullback.lift_fst, pullback.lift_fst]
      show _ ≫ s.1 = _ ≫ τ ≫ s.1
      rw [← Category.assoc _ τ, hresτ]
    · show Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ pullback.lift s₁.1 (𝟙 _) s₁.2 ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ pullback.lift s₂.1 (𝟙 _) s₂.2 ≫ pullback.snd _ _
      rw [pullback.lift_snd, pullback.lift_snd]

  haveI : FormallyUnramified (L'.schemeNsmul k) :=
    RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing L'
      (fun t x y => (RelativeGroupLaw.IsCommutative.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) hcomm) t x y) k
      (isUnit_natCast_of_liesOverPrime hp A hA k hk)
  haveI : LocallyOfFiniteType (L'.schemeNsmul k) := by
    haveI := hlfp k hk0
    rw [show L'.schemeNsmul k = _ from schemeNsmul_baseChange_eq_map (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L k]
    exact MorphismProperty.pullbackMap (P := @LocallyOfFiniteType) inferInstance inferInstance
      (L.schemeNsmul_over k).symm (Category.id_comp _).symm
  have heq : u₁.1 = u₂.1 :=
    AlgebraicGeometry.eq_of_comp_eq_of_residue_comp_eq_of_formallyUnramified (L'.schemeNsmul k) (↥A)
      u₁.1 u₂.1 hg' hres

  have hsτ : s.1 = τ ≫ s.1 := by
    have e := congrArg (· ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) heq
    change pullback.lift s₁.1 (𝟙 _) s₁.2 ≫ pullback.fst _ _ = pullback.lift s₂.1 (𝟙 _) s₂.2 ≫ pullback.fst _ _ at e
    rwa [pullback.lift_fst, pullback.lift_fst] at e
  apply pts.injective
  apply Subtype.ext
  rw [pts_galois, hs, ← Category.assoc, hjτ, Category.assoc, ← hsτ]

theorem exists_nsmul_eq_of_extends
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g) (hcomm : L.IsCommutative)
    (hflat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (hsurj : ∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n))
    (hlfp : ∀ n : ℕ, 0 < n → LocallyOfFinitePresentation (L.schemeNsmul n))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (n : ℕ) (hn : ¬ p ∣ n) (hn0 : 0 < n) (x : JZero p)
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g)
    (hs : (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1) :
    ∃ (y : JZero p) (t : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g),
      n • y = x ∧ (pts y).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ t.1 := by
  classical
  have hp : p.Prime := Fact.out

  have h1 : pts 0 = L.one _ :=
    eq_one_of_mul_self L _ _ (by have e := pts_add 0 0; rw [add_zero] at e; exact e.symm)
  have hpow : ∀ (c : ℕ) (z : JZero p), pts (c • z) = L.nsmul _ c (pts z) := by
    intro c z
    induction c with
    | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]; exact h1
    | succ c ih => rw [succ_nsmul, pts_add, ih, RelativeGroupLaw.nsmul_succ]
  have hjι : (Spec.map (CommRingCat.ofHom A.subtype)) ≫ (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) := by
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1

  let L' := L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))
  let s₁ : SchemeHomOver (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A)))) g := ⟨s.1, by rw [Category.id_comp]; exact s.2⟩
  let u : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) :=
    RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) s₁

  have hmap := schemeNsmul_baseChange_eq_map (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) L n
  haveI : Flat (L'.schemeNsmul n) := by
    haveI := hflat n hn0
    rw [show L'.schemeNsmul n = _ from hmap]
    exact MorphismProperty.pullbackMap (P := @Flat) inferInstance inferInstance
      (L.schemeNsmul_over n).symm (Category.id_comp _).symm
  haveI : Surjective (L'.schemeNsmul n) := by
    haveI := hsurj n hn0
    rw [show L'.schemeNsmul n = _ from hmap]
    exact MorphismProperty.pullbackMap (P := @Surjective) inferInstance inferInstance
      (L.schemeNsmul_over n).symm (Category.id_comp _).symm
  haveI : LocallyOfFinitePresentation (L'.schemeNsmul n) := by
    haveI := hlfp n hn0
    rw [show L'.schemeNsmul n = _ from hmap]
    exact MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) inferInstance inferInstance
      (L.schemeNsmul_over n).symm (Category.id_comp _).symm
  haveI : FormallyUnramified (L'.schemeNsmul n) :=
    RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing L'
      (fun t x y => (RelativeGroupLaw.IsCommutative.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) hcomm) t x y) n
      (isUnit_natCast_of_liesOverPrime hp A hA n hn)

  let fY := pullback.snd (L'.schemeNsmul n) u.1
  haveI : Flat fY := MorphismProperty.pullback_snd (P := @Flat) _ _ inferInstance
  haveI : FormallyUnramified fY := MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ inferInstance
  haveI : LocallyOfFinitePresentation fY :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI : AlgebraicGeometry.Etale fY := Etale.of_formallyUnramified_of_flat (f := fY)
  have hsurjY : Surjective fY := MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
  obtain ⟨y₀, hy₀⟩ := hsurjY.surj (IsLocalRing.closedPoint ↥A)

  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨sec, hsec, -⟩ :=
    AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing fY y₀ hy₀

  have hover : (sec ≫ pullback.fst (L'.schemeNsmul n) u.1) ≫ RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g = 𝟙 _ := by
    calc (sec ≫ pullback.fst (L'.schemeNsmul n) u.1) ≫ RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g
        = sec ≫ pullback.fst (L'.schemeNsmul n) u.1 ≫
            (L'.schemeNsmul n ≫ RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := by
          rw [L'.schemeNsmul_over n, Category.assoc]
      _ = sec ≫ (pullback.fst (L'.schemeNsmul n) u.1 ≫ L'.schemeNsmul n) ≫
            RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g := by simp only [Category.assoc]
      _ = sec ≫ (pullback.snd (L'.schemeNsmul n) u.1 ≫ u.1) ≫
            RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g := by rw [pullback.condition]
      _ = (sec ≫ pullback.snd (L'.schemeNsmul n) u.1) ≫ (u.1 ≫ RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) := by
          simp only [Category.assoc]
      _ = 𝟙 _ := by rw [hsec, u.2, Category.id_comp]
  let tpt : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g) :=
    ⟨sec ≫ pullback.fst (L'.schemeNsmul n) u.1, hover⟩
  have hnt : L'.nsmul (𝟙 _) n tpt = u := by
    apply Subtype.ext
    rw [← comp_schemeNsmul]
    show (sec ≫ pullback.fst (L'.schemeNsmul n) u.1) ≫ L'.schemeNsmul n = u.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsec, Category.id_comp]
  let t := RelativeGroupLaw.baseChangePointToBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) tpt
  have hnt' : L.nsmul _ n t = s₁ := by
    rw [← baseChangePointToBase_nsmul, hnt, RelativeGroupLaw.baseChangePointToBase_ofBase]

  refine ⟨pts.symm (schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) hjι t), ⟨t.1, t.2.trans (Category.id_comp _)⟩, ?_, ?_⟩
  · apply pts.injective
    rw [hpow, Equiv.apply_symm_apply, ← L.nsmul_natural, hnt']
    exact Subtype.ext hs.symm
  · rw [Equiv.apply_symm_apply]
    rfl

end VIAssembly

open VIAssembly

theorem solution
    (p : ℕ) [Fact p.Prime]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g) (hcomm : L.IsCommutative)
    (hflat : ∀ n : ℕ, 0 < n → Flat (L.schemeNsmul n))
    (hsurj : ∀ n : ℕ, 0 < n → Surjective (L.schemeNsmul n))
    (hlfp : ∀ n : ℕ, 0 < n → LocallyOfFinitePresentation (L.schemeNsmul n))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y))
    (pts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hExt : ∀ y ∈ inertiaInvariantPoints p A,
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
        (pts (eisensteinNumerator p • y)).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1)
    (m : ℕ) (hm : ¬ p ∣ m) :
    {x : JZero p | x ∈ jZeroTorsion p m ∧
        ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) g,
          (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
      = (jZeroToricTorsion p A m : Set (JZero p)) := by
  have hp : p.Prime := Fact.out
  have hn : ¬ p ∣ eisensteinNumerator p := by
    intro h
    have hc := Nat.Coprime.coprime_dvd_left h (eisensteinNumerator_coprime p hp.ne_zero)
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 hc)
  have hn0 : 0 < eisensteinNumerator p := by
    have h1 : 1 ≤ p - 1 := by have := hp.two_le; omega
    exact Nat.div_pos (Nat.le_of_dvd h1 (Nat.gcd_dvd_left _ _)) (Nat.gcd_pos_of_pos_left _ h1)
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_jZeroToricTorsion]
  constructor
  · rintro ⟨hxm, s, hs⟩
    refine ⟨hxm, ?_⟩
    obtain ⟨y, t, hy, ht⟩ := exists_nsmul_eq_of_extends p g L hcomm hflat hsurj hlfp pts pts_add A hA
      (eisensteinNumerator p) hn hn0 x s hs
    refine ⟨y, ?_, hy⟩

    have hxm' : m • x = 0 := by
      have h := (Submodule.mem_torsionBy_iff (R := ℤ) _ _).1 hxm
      rwa [natCast_zsmul] at h
    have hynm : (eisensteinNumerator p * m) • y = 0 := by
      rw [mul_comm, mul_smul, hy, hxm']
    exact mem_inertiaInvariantPoints_of_extends p g L hcomm hlfp pts pts_add pts_galois A hA
      (eisensteinNumerator p * m) (by
        intro h; rcases (Nat.Prime.dvd_mul hp).1 h with h | h; exact hn h; exact hm h) y hynm t ht
  · rintro ⟨hxm, y, hy, rfl⟩
    exact ⟨hxm, hExt y hy⟩

end S_ModularCurve_setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion
end P2MW
export P2MW.S_ModularCurve_setOf_mem_jZeroTorsion_and_exists_schemeHomOver_eq_coe_jZeroToricTorsion (solution)

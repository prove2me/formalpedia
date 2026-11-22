-- Prove2me | solution 1 for MasulloGRH.tateIdeleDomain_existsUnique_principal_mul
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T13:03:13.256713+00:00
-- url     : https://prove2.me/submissions/416f0de0-edbf-4665-9a08-5577bdd12553

import Mathlib
import Definitions.Def_MasulloGRH_TateIdeleDomain
import Theorems.Thm_MasulloGRH_tateArchimedeanDomain_existsUnique_unit_mul
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateIdeleDomain_existsUnique_principal_mul

open MasulloGRH RiemannMasullo
open scoped nonZeroDivisors NNReal WithZero

variable {F : Type*} [Field F] [NumberField F]

/-! ### Finite components of an idele -/

/-- The finite component at `v` of an idele times that of its inverse is `1`. -/
lemma fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) h
  exact h2

/-- The component of an idele at a finite place `v` has valuation `1` if and only if it and the
`v`-component of the inverse idele are `v`-integral. -/
lemma valued_eq_one_iff (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 ↔
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
        ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  have hm : Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
      Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
    rw [← map_mul, fin_mul_inv, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hm
    exact ⟨h.le, hm.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
          Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) := hm.symm
      _ ≤ Valued.v ((g : AdeleRing (𝓞 F) F).2 v) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _

/-- If the `v`-components of an idele and of its inverse are both `v`-integral, the `v`-component
has norm `1`. -/
lemma norm_fin_eq_one_of_mem (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have a1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1)
  have a2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h2)
  have hm : ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
      ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, fin_mul_inv, norm_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ) = ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
        ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ := hm.symm
    _ ≤ ‖(g : AdeleRing (𝓞 F) F).2 v‖ * 1 := mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    _ = _ := mul_one _

/-- An idele is a unit at all but finitely many finite places. -/
lemma finite_valued_ne_one (g : IdeleGroup F) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v ((g : AdeleRing (𝓞 F) F).2 v) ≠ 1}.Finite := by
  have h1 : ∀ᶠ v in Filter.cofinite,
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := (g : AdeleRing (𝓞 F) F).2.2
  have h2 : ∀ᶠ v in Filter.cofinite,
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2
  have h3 := h1.and h2
  rw [Filter.eventually_cofinite] at h3
  refine h3.subset ?_
  intro v hv h
  exact hv ((valued_eq_one_iff g v).mpr h)

/-- All but finitely many finite components of an idele have norm `1`. -/
lemma finite_mulSupport_fin (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  refine (finite_valued_ne_one g).subset ?_
  intro v hv h
  exact hv (norm_fin_eq_one_of_mem g v ((valued_eq_one_iff g v).mp h).1
    ((valued_eq_one_iff g v).mp h).2)

/-! ### The idelic norm -/

/-- The idelic norm is multiplicative. -/
lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := fun w => rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  simp only [e1, e2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (finite_mulSupport_fin g) (finite_mulSupport_fin h)]
  ring

/-- On the ideles that are units at every finite place, the idelic norm is the archimedean
norm. -/
lemma ideleNorm_eq_of_units (g : IdeleGroup F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1) :
    ideleNorm g = ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  unfold ideleNorm
  rw [finprod_eq_one_of_forall_eq_one (fun v => norm_fin_eq_one_of_mem g v
    ((valued_eq_one_iff g v).mp (hg v)).1 ((valued_eq_one_iff g v).mp (hg v)).2), mul_one]

/-- The archimedean idele norm, as a real number, is the product of the normalized absolute
values. -/
lemma coe_infiniteIdeleNorm (g : (InfiniteAdeleRing F)ˣ) :
    (((infiniteIdeleNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      ∏ w : InfinitePlace F, ‖(g : InfiniteAdeleRing F) w‖ ^ w.mult := by
  simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val, NNReal.coe_prod,
    NNReal.coe_pow]
  rfl

/-- The product formula: a principal idele has idelic norm `1`. -/
lemma ideleNorm_principalIdele (k : Fˣ) : ideleNorm (principalIdele F k) = 1 := by
  have h := NumberField.prod_abs_eq_one (K := F) (x := (k : F)) k.ne_zero
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h
  rw [← h]
  unfold ideleNorm
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe w _

/-! ### The archimedean and the finite part of an idele -/

/-- The finite part of an idele. -/
noncomputable def finPart : IdeleGroup F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

/-- The archimedean part of an idele. -/
noncomputable def infPart : IdeleGroup F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

lemma finPart_apply (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((finPart g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      (g : AdeleRing (𝓞 F) F).2 v := rfl

lemma finPart_inv_apply (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (((finPart g)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v := by
  rw [← map_inv]
  rfl

lemma infPart_val (g : IdeleGroup F) :
    ((infPart g : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = (g : AdeleRing (𝓞 F) F).1 :=
  rfl

/-- The finite part of an idele lies in the group `∏_v 𝒪_vˣ` if and only if all its finite
components have valuation `1`. -/
lemma finPart_mem_unitIdeles_iff (g : IdeleGroup F) :
    finPart g ∈ FiniteAdeleRing.unitIdeles (𝓞 F) F ↔
      ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff]
  constructor
  · rintro ⟨h1, h2⟩ v
    refine (valued_eq_one_iff g v).mpr ⟨h1 v, ?_⟩
    have h := h2 v
    rwa [finPart_inv_apply] at h
  · intro h
    refine ⟨fun v => ((valued_eq_one_iff g v).mp (h v)).1, fun v => ?_⟩
    rw [finPart_inv_apply]
    exact ((valued_eq_one_iff g v).mp (h v)).2

/-- The finite part of a principal idele is the diagonal image in the finite ideles. -/
lemma finPart_principalIdele (k : Fˣ) :
    finPart (principalIdele F k) =
      Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) k :=
  Units.ext rfl

/-- The global unit `u`, as an element of `Fˣ`. -/
def unitToField : (𝓞 F)ˣ →* Fˣ := Units.map (algebraMap (𝓞 F) F).toMonoidHom

/-- The archimedean part of the principal idele of a global unit is its diagonal image in the
archimedean ideles. -/
lemma infPart_principalIdele_unit (u : (𝓞 F)ˣ) :
    infPart (principalIdele F (unitToField u)) = unitsToInfiniteIdeles F u :=
  Units.ext rfl

lemma finPart_unit_integral (u : (𝓞 F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((finPart (principalIdele F (unitToField u)) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (((algebraMap (𝓞 F) F (u : 𝓞 F) : F) : v.adicCompletion F)) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one _

/-- The principal idele of a global unit is a unit at every finite place. -/
lemma finPart_unit_mem (u : (𝓞 F)ˣ) :
    finPart (principalIdele F (unitToField u)) ∈ FiniteAdeleRing.unitIdeles (𝓞 F) F := by
  rw [FiniteAdeleRing.mem_unitIdeles_iff]
  refine ⟨fun v => finPart_unit_integral u v, fun v => ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv]
  exact finPart_unit_integral u⁻¹ v

/-- An element of `Fˣ` of valuation `1` at every finite place is a global unit. -/
lemma exists_unit_of_valuation_eq_one (η : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (η : F) = 1) :
    ∃ u : (𝓞 F)ˣ, unitToField u = η := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (η : F)
    (fun v => (h v).le)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((η⁻¹ : Fˣ) : F)
    (fun v => by rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one])
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩

/-! ### The ideal class of an idele -/

/-- An invertible fractional ideal with trivial class is principal. -/
lemma mem_range_of_mk_eq_one (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (h : ClassGroup.mk F I = 1) :
    I ∈ (toPrincipalIdeal (𝓞 F) F).range := by
  rw [ClassGroup.mk_eq_one_iff] at h
  obtain ⟨x, hx⟩ := h.principal
  rw [mem_principal_ideals_iff]
  refine ⟨x, ?_⟩
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) =
    ((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
  rw [FractionalIdeal.coe_spanSingleton, hx]

/-- The class of a principal fractional ideal is trivial. -/
lemma mk_toPrincipalIdeal (k : Fˣ) :
    ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F k) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  exact ⟨⟨(k : F), by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩⟩

/-- The content homomorphism `φ` from the finite ideles onto the invertible fractional ideals:
the ideal class of an idele is the class of `φ` of its finite part, `φ` sends the diagonal image
of `k ∈ Fˣ` to the principal ideal `(k)`, and its kernel is `∏_v 𝒪_vˣ`. -/
theorem exists_contentHom (F : Type*) [Field F] [NumberField F] :
    ∃ φ : (FiniteAdeleRing (𝓞 F) F)ˣ →* (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      (∀ g : IdeleGroup F, ideleIdealClass F g = ClassGroup.mk F (φ (finPart g))) ∧
      (∀ k : Fˣ, φ (finPart (principalIdele F k)) = toPrincipalIdeal (𝓞 F) F k) ∧
      φ.ker = FiniteAdeleRing.unitIdeles (𝓞 F) F := by
  obtain ⟨φ, hφ, hprin, -, hker, -⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
      (𝓞 F) F
  refine ⟨φ, ?_, ?_, hker⟩
  · intro g
    let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
      -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))
    let P : HeightOneSpectrum (𝓞 F) → (Ideal (𝓞 F))⁰ := fun v =>
      ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
    have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (FractionalIdeal.mk0 F (P v)) ^ n v).Finite := by
      refine (finite_valued_ne_one g).subset ?_
      intro v hv h
      apply hv
      change (FractionalIdeal.mk0 F (P v)) ^
        (-WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))) = 1
      rw [h, WithZero.log_one, neg_zero, zpow_zero]
    have hu : φ (finPart g) = ∏ᶠ v, (FractionalIdeal.mk0 F (P v)) ^ n v := by
      apply Units.ext
      rw [hφ (finPart g)]
      have h1 := MonoidHom.map_finprod_of_injective (Units.coeHom (FractionalIdeal (𝓞 F)⁰ F))
        (fun _ _ h => Units.ext h) (fun v => (FractionalIdeal.mk0 F (P v)) ^ n v)
      rw [Units.coeHom_apply] at h1
      rw [h1]
      refine finprod_congr fun v => ?_
      rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, FractionalIdeal.coe_mk0]
      rfl
    rw [hu, MonoidHom.map_finprod _ hfin]
    unfold ideleIdealClass
    refine finprod_congr fun v => ?_
    rw [map_zpow, ClassGroup.mk_mk0]
  · intro k
    rw [finPart_principalIdele]
    exact hprin k

end Sol_MasulloGRH_tateIdeleDomain_existsUnique_principal_mul

open MasulloGRH Sol_MasulloGRH_tateIdeleDomain_existsUnique_principal_mul

theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1)
    (hr : ∀ c : ClassGroup (𝓞 F), ideleIdealClass F (r c) = c)
    (g : IdeleGroup F) (hg : ideleNorm g = 1) :
    ∃! ξ : Fˣ, ∃ e ∈ tateIdeleDomain F b v₀ σ r, g = principalIdele F ξ * e := by
  obtain ⟨φ, hcls, hprin, hker⟩ := exists_contentHom F
  -- the ideal class map, as a homomorphism
  let cls : IdeleGroup F →* ClassGroup (𝓞 F) := (ClassGroup.mk F).comp (φ.comp finPart)
  have hcls' : ∀ x : IdeleGroup F, ideleIdealClass F x = cls x := hcls
  have hcls_p : ∀ ξ : Fˣ, cls (principalIdele F ξ) = 1 := by
    intro ξ
    change ClassGroup.mk F (φ (finPart (principalIdele F ξ))) = 1
    rw [hprin]
    exact mk_toPrincipalIdeal ξ
  have hcls_e : ∀ e : IdeleGroup F,
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((e : AdeleRing (𝓞 F) F).2 v) = 1) →
        cls e = 1 := by
    intro e he
    have h1 : φ (finPart e) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact (finPart_mem_unitIdeles_iff e).mpr he
    change ClassGroup.mk F (φ (finPart e)) = 1
    rw [h1, map_one]
  refine existsUnique_of_exists_of_unique ?_ ?_
  · -- existence
    obtain ⟨c, hc⟩ : ∃ c, c = ideleIdealClass F g := ⟨_, rfl⟩
    have h1 : cls ((r c)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, ← hcls' (r c), hr c, ← hcls' g, ← hc]
      exact inv_mul_cancel c
    obtain ⟨ξ, hξ⟩ := mem_range_of_mk_eq_one (φ (finPart ((r c)⁻¹ * g))) h1
    obtain ⟨k, hk⟩ : ∃ k, k = (principalIdele F ξ)⁻¹ * ((r c)⁻¹ * g) := ⟨_, rfl⟩
    have hkfin : finPart k ∈ FiniteAdeleRing.unitIdeles (𝓞 F) F := by
      rw [← hker, MonoidHom.mem_ker, hk, map_mul, map_mul, map_inv, map_inv, hprin, hξ]
      exact inv_mul_cancel _
    have hkval := (finPart_mem_unitIdeles_iff k).mp hkfin
    have hknorm : ideleNorm k = 1 := by
      have e1 : ideleNorm (principalIdele F ξ) * ideleNorm k = ideleNorm ((r c)⁻¹ * g) := by
        rw [← ideleNorm_mul, hk, mul_inv_cancel_left]
      have e2 : ideleNorm (r c) * ideleNorm ((r c)⁻¹ * g) = ideleNorm g := by
        rw [← ideleNorm_mul, mul_inv_cancel_left]
      rw [hrn, one_mul, hg] at e2
      rw [ideleNorm_principalIdele, one_mul, e2] at e1
      exact e1
    have hkinf : RiemannMasullo.infiniteIdeleNorm F (infPart k) = 1 := by
      apply Units.ext
      apply NNReal.coe_injective
      rw [coe_infiniteIdeleNorm, Units.val_one, NNReal.coe_one, ← hknorm,
        ideleNorm_eq_of_units k hkval]
      rfl
    obtain ⟨u, ⟨a, ha, hua⟩, -⟩ :=
      MasulloGRH.tateArchimedeanDomain_existsUnique_unit_mul F b v₀ σ ⟨infPart k, hkinf⟩
    have hua' : infPart k = unitsToInfiniteIdeles F u * (a : (InfiniteAdeleRing F)ˣ) := hua
    obtain ⟨e, he⟩ : ∃ e, e = (principalIdele F (unitToField u))⁻¹ * k := ⟨_, rfl⟩
    have heinf : infPart e = (a : (InfiniteAdeleRing F)ˣ) := by
      rw [he, map_mul, map_inv, infPart_principalIdele_unit, hua', inv_mul_cancel_left]
    have hefin : finPart e ∈ FiniteAdeleRing.unitIdeles (𝓞 F) F := by
      rw [he, map_mul, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (finPart_unit_mem u)) hkfin
    refine ⟨ξ * unitToField u, r c * e, ⟨c, e, ⟨⟨a, ha, ?_⟩, ?_⟩, rfl⟩, ?_⟩
    · exact congrArg Units.val heinf
    · exact (finPart_mem_unitIdeles_iff e).mp hefin
    · rw [map_mul, he, hk, mul_left_comm (r c), mul_left_comm (r c), mul_inv_cancel_left,
        mul_assoc, mul_inv_cancel_left, mul_inv_cancel_left]
  · -- uniqueness
    rintro ξ₁ ξ₂ ⟨_, ⟨c₁, e₁, ⟨⟨a₁, ha₁, hea₁⟩, hv₁⟩, rfl⟩, h₁⟩
      ⟨_, ⟨c₂, e₂, ⟨⟨a₂, ha₂, hea₂⟩, hv₂⟩, rfl⟩, h₂⟩
    have hc₁ : cls g = c₁ := by
      rw [h₁, map_mul, map_mul, hcls_p, hcls_e e₁ hv₁, ← hcls', hr, one_mul, mul_one]
    have hc₂ : cls g = c₂ := by
      rw [h₂, map_mul, map_mul, hcls_p, hcls_e e₂ hv₂, ← hcls', hr, one_mul, mul_one]
    have hc : c₁ = c₂ := hc₁.symm.trans hc₂
    subst hc
    have h3 : principalIdele F ξ₁ * e₁ = principalIdele F ξ₂ * e₂ := by
      have h := h₁.symm.trans h₂
      rw [mul_left_comm, mul_left_comm (principalIdele F ξ₂)] at h
      exact mul_left_cancel h
    obtain ⟨η, hη⟩ : ∃ η, η = ξ₂⁻¹ * ξ₁ := ⟨_, rfl⟩
    have h4 : e₂ = principalIdele F η * e₁ := by
      rw [hη, map_mul, map_inv, mul_assoc, h3, inv_mul_cancel_left]
    have h5 : principalIdele F η = e₂ * e₁⁻¹ := by
      rw [h4, mul_inv_cancel_right]
    have h6 : finPart (principalIdele F η) ∈ FiniteAdeleRing.unitIdeles (𝓞 F) F := by
      rw [h5, map_mul, map_inv]
      exact Subgroup.mul_mem _ ((finPart_mem_unitIdeles_iff e₂).mpr hv₂)
        (Subgroup.inv_mem _ ((finPart_mem_unitIdeles_iff e₁).mpr hv₁))
    have h7 : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (η : F) = 1 := by
      intro v
      have h := (finPart_mem_unitIdeles_iff _).mp h6 v
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact h
    obtain ⟨u, hu⟩ := exists_unit_of_valuation_eq_one η h7
    have h8 : (a₂ : (InfiniteAdeleRing F)ˣ) =
        unitsToInfiniteIdeles F u * (a₁ : (InfiniteAdeleRing F)ˣ) := by
      have h := congrArg infPart h4
      rw [map_mul, ← hu, infPart_principalIdele_unit] at h
      have i₁ : infPart e₁ = (a₁ : (InfiniteAdeleRing F)ˣ) := Units.ext hea₁
      have i₂ : infPart e₂ = (a₂ : (InfiniteAdeleRing F)ˣ) := Units.ext hea₂
      rw [i₁, i₂] at h
      exact h
    obtain ⟨u₀, -, huniq⟩ :=
      MasulloGRH.tateArchimedeanDomain_existsUnique_unit_mul F b v₀ σ a₂
    have hu₁ : u = u₀ := huniq u ⟨a₁, ha₁, h8⟩
    have hu₂ : (1 : (𝓞 F)ˣ) = u₀ := huniq 1 ⟨a₂, ha₂, by rw [map_one, one_mul]⟩
    have hu₃ : u = 1 := hu₁.trans hu₂.symm
    rw [hu₃, map_one] at hu
    rw [hη] at hu
    exact (inv_mul_eq_one.mp hu.symm).symm

-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/af77186a-3f76-5384-9c15-ecf4dce62b24

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_groupCohomology_exists_carry_H2pi_eq
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion.NumberField IsDedekindDomain"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk PlaceDecomp.decomp PlaceDecomp.coe_smul_units PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom PlaceDecomp.exists_fundamentalClass_units_adicCompletion"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp coe_smul_units forall_smul_eq_iff_mem_range_adicCompletionSemialgHom exists_fundamentalClass_units_adicCompletion"
namespace NormIndexCyc
p2m_open "NumberField.PlaceDecomp NumberField"

theorem carryFun_add {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (x y : A) :
    carryFun s hs hfin (x + y) = carryFun s hs hfin x + carryFun s hs hfin y := by
  funext p
  simp only [carryFun, Pi.add_apply]
  split_ifs <;> simp

theorem carryFun_zero {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} : carryFun s hs hfin (0 : A) = 0 := by
  funext p
  simp only [carryFun, Pi.zero_apply]
  split_ifs <;> simp

theorem sum_range_orderOf_eq_sum {Q : Type} [Group Q] [Fintype Q] {X : Type} [AddCommMonoid X]
    (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t) (f : Q → X) :
    ∑ i ∈ Finset.range (orderOf t), f (t ^ i) = ∑ c : Q, f c := by
  classical
  rw [Finset.sum_range (fun i => f (t ^ i))]
  have htop : Subgroup.zpowers t = ⊤ := by
    rw [eq_top_iff]; intro g _; exact ht g
  let e : Fin (orderOf t) ≃ Q :=
    (finEquivZPowers htfin).trans ((MulEquiv.subgroupCongr htop).toEquiv.trans Subgroup.topEquiv.toEquiv)
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  congr 1

theorem forall_ρ_eq_of_ρ_gen_eq {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (hfin : IsOfFinOrder t)
    {Mu : Type} [CommGroup Mu] [MulDistribMulAction Q Mu] (a : Rep.ofMulDistribMulAction Q Mu)
    (ha : (Rep.ofMulDistribMulAction Q Mu).ρ t a = a) (g : Q) : (Rep.ofMulDistribMulAction Q Mu).ρ g a = a := by
  obtain ⟨n, rfl⟩ := (hfin.mem_powers_iff_mem_zpowers).2 (ht g)
  rw [map_pow]
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ha, ih]

theorem natCard_eq_natCard_res_top {G : Type} [Group G] {Mu : Type} [CommGroup Mu] [MulDistribMulAction G Mu] (n : ℕ) :
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Mu) n) =
      Nat.card (groupCohomology (Rep.res (⊤ : Subgroup G).subtype (Rep.ofMulDistribMulAction G Mu)) n) := by
  let A := Rep.ofMulDistribMulAction G Mu
  let eT : G →* ↥(⊤ : Subgroup G) := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.toMonoidHom
  have key1 : groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n ≫
      groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype A))) n = 𝟙 _ := by
    rw [← groupCohomology.map_comp]
    exact groupCohomology.map_id (B := A) (n := n)
  have key2 : groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype A))) n ≫
      groupCohomology.map (⊤ : Subgroup G).subtype
        (𝟙 (Rep.res (⊤ : Subgroup G).subtype (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype A)))) n = 𝟙 _ := by
    rw [← groupCohomology.map_comp]
    exact groupCohomology.map_id (B := Rep.res (⊤ : Subgroup G).subtype A) (n := n)
  refine Nat.card_congr (Equiv.mk
    (fun x => (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom x)
    (fun y => (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype A))) n).hom y)
    (fun x => ?_) (fun y => ?_))
  · have hz := congrArg (fun T => (ModuleCat.Hom.hom T) x) key1
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hz
    exact hz
  · have hz := congrArg (fun T => (ModuleCat.Hom.hom T) y) key2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hz
    exact hz

end NumberField.PlaceDecomp.NormIndexCyc

open NumberField.PlaceDecomp.NormIndexCyc in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)

    (t : ↥(NumberField.PlaceDecomp.decomp E F w))
    (ht : ∀ g : ↥(NumberField.PlaceDecomp.decomp E F w), g ∈ Subgroup.zpowers t) (hfin : IsOfFinOrder t) :
    ∃ Ψ : (v.adicCompletion E)ˣ →*
        Multiplicative (groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),

      (∀ (a : (v.adicCompletion E)ˣ)
         (hc : carryFun (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) t ht hfin
            (Additive.ofMul (Units.map
              (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
                v.adicCompletion E →* w.adicCompletion F) a)) ∈
            groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)),
         Ψ a = Multiplicative.ofAdd
           ((groupCohomology.H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom
             ⟨carryFun (A := Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) t ht hfin
               (Additive.ofMul (Units.map
                 (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
                   v.adicCompletion E →* w.adicCompletion F) a)), hc⟩)) ∧

      Function.Surjective Ψ ∧

      (∀ a : (v.adicCompletion E)ˣ, Ψ a = 1 ↔
         ∃ b : (w.adicCompletion F)ˣ,
           (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
             IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) (a : v.adicCompletion E)) ∧

      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) =
        Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) := by
  classical
  subst hw
  haveI : Fintype (↥(NumberField.PlaceDecomp.decomp E F w)) := Fintype.ofFinite _

  set ι := IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : (w.under (𝓞 E)).Extension (𝓞 F)) with hιdef
  set ιu : ((w.under (𝓞 E)).adicCompletion E)ˣ →* (w.adicCompletion F)ˣ := Units.map (ι : (w.under (𝓞 E)).adicCompletion E →* w.adicCompletion F) with hιudef
  have hιu_coe : ∀ a : ((w.under (𝓞 E)).adicCompletion E)ˣ, ((ιu a : (w.adicCompletion F)ˣ) : w.adicCompletion F) = ι (a : (w.under (𝓞 E)).adicCompletion E) :=
    fun a => rfl

  have hfixF : ∀ (a : ((w.under (𝓞 E)).adicCompletion E)ˣ) (σ : (↥(NumberField.PlaceDecomp.decomp E F w))), σ • ι (a : (w.under (𝓞 E)).adicCompletion E) = ι (a : (w.under (𝓞 E)).adicCompletion E) :=
    fun a σ => (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w _).2 ⟨_, rfl⟩ σ
  have hfixU : ∀ (a : ((w.under (𝓞 E)).adicCompletion E)ˣ) (σ : (↥(NumberField.PlaceDecomp.decomp E F w))), σ • ιu a = ιu a :=
    fun a σ => Units.ext (by rw [NumberField.PlaceDecomp.coe_smul_units, hιu_coe, hfixF])
  have hρ : ∀ (a : ((w.under (𝓞 E)).adicCompletion E)ˣ) (σ : (↥(NumberField.PlaceDecomp.decomp E F w))),
      (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ).ρ σ (Additive.ofMul (ιu a)) = Additive.ofMul (ιu a) := fun a σ => by
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]; exact congrArg Additive.ofMul (hfixU a σ)

  let Ψ₀ : ((w.under (𝓞 E)).adicCompletion E)ˣ → groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) := fun a =>
    (H2π (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)).hom ⟨carryFun (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) t ht hfin (Additive.ofMul (ιu a)),
      groupCohomology.carryFun_mem_cocycles2 t ht hfin _ (hρ a t)⟩
  have Ψ₀_mul : ∀ a b, Ψ₀ (a * b) = Ψ₀ a + Ψ₀ b := by
    intro a b
    change (H2π _).hom _ = (H2π _).hom _ + (H2π _).hom _
    rw [← map_add]
    congr 1
    apply Subtype.ext
    change carryFun t ht hfin _ = carryFun t ht hfin _ + carryFun t ht hfin _
    rw [← carryFun_add]
    exact congrArg (carryFun t ht hfin) (by rw [map_mul]; rfl)
  have Ψ₀_one : Ψ₀ 1 = 0 := by
    have h := Ψ₀_mul 1 1
    rw [mul_one, left_eq_add] at h
    exact h
  let Ψ : ((w.under (𝓞 E)).adicCompletion E)ˣ →* Multiplicative (groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) :=
    { toFun := fun a => Multiplicative.ofAdd (Ψ₀ a)
      map_one' := by rw [Ψ₀_one]; rfl
      map_mul' := fun a b => by rw [Ψ₀_mul, ofAdd_add] }
  have Ψ_apply : ∀ a, Ψ a = Multiplicative.ofAdd (Ψ₀ a) := fun a => rfl
  refine ⟨Ψ, fun a hc => rfl, ?_, ?_, ?_⟩
  ·
    intro c
    induction h : Multiplicative.toAdd c using H2_induction_on generalizing c with
    | h z =>
      obtain ⟨hρz, hmem, heq⟩ := groupCohomology.exists_carry_H2pi_eq t ht hfin z
      set γ : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) := cyclicInv t ⇑z with hγ
      have hγfix : ∀ σ : (↥(NumberField.PlaceDecomp.decomp E F w)), σ • ((Additive.toMul (α := (w.adicCompletion F)ˣ) γ : (w.adicCompletion F)ˣ) :
          w.adicCompletion F) = ((Additive.toMul (α := (w.adicCompletion F)ˣ) γ : (w.adicCompletion F)ˣ) : w.adicCompletion F) := by
        intro σ
        have h1 := forall_ρ_eq_of_ρ_gen_eq t ht hfin γ hρz σ
        rw [Rep.ofMulDistribMulAction_ρ_apply_apply] at h1
        have h1' : σ • Additive.toMul (α := (w.adicCompletion F)ˣ) γ = Additive.toMul (α := (w.adicCompletion F)ˣ) γ := by
          have := congrArg (Additive.toMul (α := (w.adicCompletion F)ˣ)) h1
          simpa only [toMul_ofMul] using this
        have h2 := congrArg (fun y : (w.adicCompletion F)ˣ => (y : w.adicCompletion F)) h1'
        rwa [NumberField.PlaceDecomp.coe_smul_units] at h2
      obtain ⟨a₀, ha₀⟩ := (NumberField.PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom E F w _).1 hγfix
      have ha₀0 : a₀ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at ha₀
        exact (Additive.toMul (α := (w.adicCompletion F)ˣ) γ).ne_zero ha₀.symm
      refine ⟨Units.mk0 a₀ ha₀0, ?_⟩
      have hιa : ιu (Units.mk0 a₀ ha₀0) = Additive.toMul (α := (w.adicCompletion F)ˣ) γ := Units.ext ha₀
      rw [Ψ_apply, ← ofAdd_toAdd c, h, ← heq]
      congr 1
      change (H2π _).hom _ = (H2π _).hom _
      congr 1
      apply Subtype.ext
      change carryFun t ht hfin (Additive.ofMul (ιu (Units.mk0 a₀ ha₀0))) = carryFun t ht hfin γ
      rw [hιa]
      rfl
  ·
    intro a
    rw [Ψ_apply, ofAdd_eq_one]
    change (H2π _).hom _ = 0 ↔ _
    refine (groupCohomology.carry_H2pi_eq_zero_iff t ht hfin (A := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) (Additive.ofMul (ιu a)) (hρ a t) _).trans ?_
    have key : ∀ b : (w.adicCompletion F)ˣ,
        (Additive.ofMul (α := (w.adicCompletion F)ˣ) (∏ᶠ σ : (↥(NumberField.PlaceDecomp.decomp E F w)), σ • b) : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) =
          ∑ i ∈ Finset.range (orderOf t), (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ).ρ (t ^ i) (Additive.ofMul b) := by
      intro b
      rw [finprod_eq_prod_of_fintype, ofMul_prod,
        ← sum_range_orderOf_eq_sum t ht hfin (fun σ => (Additive.ofMul (α := (w.adicCompletion F)ˣ) (σ • b) : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
      rfl
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨Additive.toMul (α := (w.adicCompletion F)ˣ) b, ?_⟩
      rw [← hιu_coe]
      have h1 : (Additive.ofMul (α := (w.adicCompletion F)ˣ) (∏ᶠ σ : (↥(NumberField.PlaceDecomp.decomp E F w)), σ • Additive.toMul (α := (w.adicCompletion F)ˣ) b) : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) =
          Additive.ofMul (ιu a) := (key _).trans hb
      exact congrArg (fun y : (w.adicCompletion F)ˣ => (y : w.adicCompletion F)) (Additive.ofMul.injective h1)
    · rintro ⟨b, hb⟩
      refine ⟨Additive.ofMul b, ?_⟩
      have hb' : (∏ᶠ σ : (↥(NumberField.PlaceDecomp.decomp E F w)), σ • b) = ιu a := Units.ext (by rw [hb, hιu_coe])
      exact (key b).symm.trans (congrArg Additive.ofMul hb')
  ·
    obtain ⟨u₀, -, h2card, -⟩ := NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion E F w
    haveI : Fintype (↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E F w)))) := Fintype.ofFinite _
    rw [natCard_eq_natCard_res_top 2, h2card ⊤, ← Nat.card_eq_fintype_card, Subgroup.card_top]

end S_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_carryClassHom_surjective_ker_eq_norms_adicCompletion (solution)

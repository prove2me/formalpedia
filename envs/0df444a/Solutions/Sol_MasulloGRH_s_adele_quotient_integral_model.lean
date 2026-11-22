-- Prove2me | solution 1 for MasulloGRH.s_adele_quotient_integral_model
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:35:54.372706+00:00
-- url     : https://prove2.me/submissions/fb04730b-7d94-46aa-b4eb-20f45e783e4b

import Mathlib
import Definitions.Def_RiemannMasullo_IntegralAdeleDiagonal
import Definitions.Def_MasulloGRH_SAdeles
import Theorems.Thm_MasulloGRH_adele_class_group_compact
import Theorems.Thm_MasulloGRH_s_adele_quotient_compact_divisible

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_s_adele_quotient_integral_model

variable (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- Membership in `𝔸_F(S)`: integrality at every finite place outside `S`. -/
theorem mem_iff (a : AdeleRing (𝓞 F) F) :
    a ∈ RiemannMasullo.integralAdelesOutside F Sf ↔
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → a.2 v ∈ v.adicCompletionIntegers F := by
  simp only [RiemannMasullo.integralAdelesOutside, Subring.mem_iInf]
  rfl

/-- `𝔸_F(S)` is open in `𝔸_F`. -/
theorem isOpen_integral :
    IsOpen (RiemannMasullo.integralAdelesOutside F Sf : Set (AdeleRing (𝓞 F) F)) := by
  have h : (RiemannMasullo.integralAdelesOutside F Sf : Set (AdeleRing (𝓞 F) F)) =
      Prod.snd ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf →
        a v ∈ v.adicCompletionIntegers F} := by
    ext a
    exact mem_iff F Sf a
  rw [h]
  exact (RestrictedProduct.isOpen_forall_imp_mem
    (fun v : HeightOneSpectrum (𝓞 F) ↦ Valued.isOpen_integer (v.adicCompletion F))
    (p := fun v ↦ v ∉ Sf)).preimage continuous_snd

/-- A principal adele lies in `𝔸_F(S)` exactly when it comes from an `S`-integer. -/
theorem diag_mem (x : F) :
    algebraMap F (AdeleRing (𝓞 F) F) x ∈ RiemannMasullo.integralAdelesOutside F Sf ↔
      x ∈ (Sf : Set (HeightOneSpectrum (𝓞 F))).integer F := by
  rw [mem_iff]
  change (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → Valued.v (x : v.adicCompletion F) ≤ 1) ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → v.valuation F x ≤ 1
  simp only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem main :
    let I := RiemannMasullo.integralAdelesOutside F Sf
    let D : AddSubgroup I := (RiemannMasullo.integralAdeleDiagonal F Sf).toAddMonoidHom.range
    (∃ e : (I ⧸ D) ≃ₜ+ (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F),
      ∀ x : I, e (QuotientAddGroup.mk x) = QuotientAddGroup.mk (x : AdeleRing (𝓞 F) F)) ∧
    ∃ π : (I ⧸ D) →+ (MasulloGRH.SAdeleRing F Sf ⧸ MasulloGRH.sIntegerLattice Sf),
      IsProperMap π ∧ IsOpenQuotientMap π ∧
      ∀ x : I, π (QuotientAddGroup.mk x) =
        QuotientAddGroup.mk
          (((x : AdeleRing (𝓞 F) F).1, fun v : Sf => (x : AdeleRing (𝓞 F) F).2 v) :
            MasulloGRH.SAdeleRing F Sf) := by
  intro I D
  let i : I →+ AdeleRing (𝓞 F) F := I.subtype.toAddMonoidHom
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let Q := MasulloGRH.sIntegerLattice Sf
  obtain ⟨-, -, hcomp, ht2, -, hdec, -, -⟩ := MasulloGRH.adele_class_group_compact F
  obtain ⟨-, -, hScomp, hSt2, -, -⟩ := MasulloGRH.s_adele_quotient_compact_divisible F Sf
  -- the principal adeles lying in `𝔸_F(S)` are the diagonal `S`-integers
  have hD : P.comap i = D := by
    ext a
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, (diag_mem F Sf x).mp (hx ▸ a.property)⟩,
        Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  -- `𝔸_F = F + 𝔸_F(S)`
  have hs : Function.Surjective (QuotientAddGroup.mk ∘ i : I → AdeleRing (𝓞 F) F ⧸ P) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨y, hy, ξ, rfl⟩ := hdec a
      refine ⟨⟨y, (mem_iff F Sf y).2 fun v _ => hy v⟩, QuotientAddGroup.eq.mpr ?_⟩
      change -y + (y + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∈ P
      rw [neg_add_cancel_left]
      exact ⟨ξ, rfl⟩
  let e₀ := QuotientAddGroup.map D P i hD.ge
  have hinj : Function.Injective e₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      have ha : i a ∈ P := (QuotientAddGroup.eq_zero_iff _).1 hx
      exact (QuotientAddGroup.eq_zero_iff _).2 (hD.le ha)
  let e := AddEquiv.ofBijective e₀
    ⟨hinj, QuotientAddGroup.map_surjective_of_surjective D P i hs _⟩
  have hq := QuotientAddGroup.isOpenQuotientMap_mk (N := P)
  have hq₀ := QuotientAddGroup.isOpenQuotientMap_mk (N := D)
  have hc : Continuous e := hq₀.continuous_comp_iff.mp
    (hq.continuous.comp continuous_subtype_val)
  have ho : IsOpenMap e := hq₀.isOpenMap_iff.mpr
    (hq.isOpenMap.comp (isOpen_integral F Sf).isOpenMap_subtype_val)
  let E : (I ⧸ D) ≃ₜ+ (AdeleRing (𝓞 F) F ⧸ P) :=
    ContinuousAddEquiv.mk' (e.toEquiv.toHomeomorphOfContinuousOpen hc ho) e.map_add
  refine ⟨⟨E, fun _ => rfl⟩, ?_⟩
  have hIcomp : CompactSpace (I ⧸ D) :=
    E.toHomeomorph.symm.surjective.compactSpace E.toHomeomorph.symm.continuous
  -- the projection onto the coordinates in `S`
  let p : I →+ MasulloGRH.SAdeleRing F Sf :=
    { toFun := fun x => ((x : AdeleRing (𝓞 F) F).1, fun v : Sf => (x : AdeleRing (𝓞 F) F).2 v)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hp : Continuous p := by
    change Continuous (fun x : RiemannMasullo.integralAdelesOutside F Sf =>
      (((x : AdeleRing (𝓞 F) F).1, fun v : Sf => (x : AdeleRing (𝓞 F) F).2 v) :
        MasulloGRH.SAdeleRing F Sf))
    have h1 : Continuous (fun x : RiemannMasullo.integralAdelesOutside F Sf =>
        (x : AdeleRing (𝓞 F) F).1) := continuous_fst.comp continuous_subtype_val
    have h2 : ∀ v : HeightOneSpectrum (𝓞 F),
        Continuous (fun x : RiemannMasullo.integralAdelesOutside F Sf =>
          (x : AdeleRing (𝓞 F) F).2 v) := fun v =>
      (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp continuous_subtype_val)
    have h3 : Continuous (fun x : RiemannMasullo.integralAdelesOutside F Sf =>
        fun v : Sf => (x : AdeleRing (𝓞 F) F).2 v) := continuous_pi fun v => h2 v
    exact h1.prodMk h3
  have hps : Function.Surjective p := by
    classical
    intro s
    let g : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F :=
      fun v => if hv : v ∈ Sf then s.2 ⟨v, hv⟩ else 0
    have hg : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → g v ∈ v.adicCompletionIntegers F := by
      intro v hv
      simp only [g, dif_neg hv]
      exact zero_mem _
    let fin : FiniteAdeleRing (𝓞 F) F := ⟨g, Sf.eventually_cofinite_notMem.mono hg⟩
    refine ⟨⟨(s.1, fin), (mem_iff F Sf _).2 hg⟩, Prod.ext rfl (funext fun v => ?_)⟩
    change g v = s.2 v
    simp only [g, dif_pos v.property]
  have hmap : D ≤ Q.comap p := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  let π := QuotientAddGroup.map D Q p hmap
  have hqQ := QuotientAddGroup.isOpenQuotientMap_mk (N := Q)
  have hπ : Continuous π := hq₀.continuous_comp_iff.mp (hqQ.continuous.comp hp)
  have hπs : Function.Surjective π :=
    QuotientAddGroup.map_surjective_of_surjective D Q p (hqQ.surjective.comp hps) hmap
  have hπo : IsOpenMap π := AddMonoidHom.isOpenMap_of_sigmaCompact π hπs hπ
  exact ⟨π, hπ.isProperMap, ⟨hπs, hπ, hπo⟩, fun _ => rfl⟩

end Sol_MasulloGRH_s_adele_quotient_integral_model

open MasulloGRH

theorem solution (F : Type*) [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    let I := RiemannMasullo.integralAdelesOutside F Sf
    let D : AddSubgroup I := (RiemannMasullo.integralAdeleDiagonal F Sf).toAddMonoidHom.range
    (∃ e : (I ⧸ D) ≃ₜ+ (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F),
      ∀ x : I, e (QuotientAddGroup.mk x) = QuotientAddGroup.mk (x : AdeleRing (𝓞 F) F)) ∧
    ∃ π : (I ⧸ D) →+ (SAdeleRing F Sf ⧸ sIntegerLattice Sf),
      IsProperMap π ∧ IsOpenQuotientMap π ∧
      ∀ x : I, π (QuotientAddGroup.mk x) =
        QuotientAddGroup.mk
          (((x : AdeleRing (𝓞 F) F).1, fun v : Sf => (x : AdeleRing (𝓞 F) F).2 v) :
            SAdeleRing F Sf) :=
  Sol_MasulloGRH_s_adele_quotient_integral_model.main F Sf

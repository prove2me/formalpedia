-- Prove2me | solution 1 for MasulloGRH.adele_class_group_compact
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T04:06:37.199144+00:00
-- url     : https://prove2.me/submissions/b3512f4d-8a6b-4e5c-9ed0-a3c8d9e1dc25

import Definitions.Def_NumberField_AdelicBox
import Mathlib
open Set NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AdeleClassProof
open NumberField IsDedekindDomain Set
variable (F : Type*) [Field F] [NumberField F]
private abbrev A := AdeleRing (𝓞 F) F
private abbrev D := algebraMap F (A F)
private abbrev P := AdeleRing.principalSubgroup (𝓞 F) F

private theorem principal_discrete : DiscreteTopology (P F) := by
  obtain ⟨U,hU,⟨u,hu⟩,hsub⟩ := AdelicBox.exists_isOpen_subset_adelicBox F
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hcont : Continuous (fun z : P F => (z:A F)+u) := continuous_subtype_val.add continuous_const
  have he : (fun z : P F => (z:A F)+u) ⁻¹' U = ({0}:Set (P F)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨k,hk⟩ := z.prop
      obtain ⟨b,hb,huq⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F u
      have hzero : (0:F)=b := huq 0 (by simpa using hsub hu)
      have hk' : k=b := huq k (by dsimp only; rw [hk]; exact hsub hz)
      have h : k=0 := hk'.trans hzero.symm
      apply Set.mem_singleton_iff.mpr
      exact Subtype.ext (by simpa [h] using hk.symm)
    · rintro rfl; simpa using hu
  rw [←he]; exact hU.preimage hcont

private theorem quotient_compact : CompactSpace (A F ⧸ P F) := by
  obtain ⟨C,hC,hbox⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  have hu : (QuotientAddGroup.mk : A F → A F ⧸ P F) '' C = univ := by
    apply eq_univ_iff_forall.mpr
    intro u
    refine QuotientAddGroup.induction_on u (fun a => ?_)
    obtain ⟨k,hk,_⟩ := AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F a
    refine ⟨D F k+a,hbox hk,QuotientAddGroup.eq_iff_sub_mem.mpr ⟨k,?_⟩⟩
    change D F k=D F k+a-a; abel
  exact isCompact_univ_iff.mp (hu ▸ hC.image QuotientAddGroup.continuous_mk)

private theorem quotient_division (n : ℕ) (hn : 0<n) : Function.Bijective
    (fun x : A F ⧸ P F => n • x) := by
  let m := QuotientAddGroup.mk' (P F)
  let r := D F (n:F)⁻¹
  have hnF : (n:F) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : r*(n:A F)=1 := by
    change D F (n:F)⁻¹*(n:A F)=1
    rw [← map_natCast (D F) n,←map_mul,inv_mul_cancel₀ hnF,map_one]
  have hcancel (x : A F) : r*(n • x)=x := by
    rw [nsmul_eq_mul,←mul_assoc,hr,one_mul]
  constructor
  · intro x y h
    obtain ⟨a,rfl⟩ := QuotientAddGroup.mk'_surjective (P F) x
    obtain ⟨b,rfl⟩ := QuotientAddGroup.mk'_surjective (P F) y
    have hab : m (n • a) = m (n • b) := by simpa only [map_nsmul] using h
    have hs : n • a - n • b ∈ P F := QuotientAddGroup.eq_iff_sub_mem.mp hab
    obtain ⟨k,hk⟩ := hs
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨(n:F)⁻¹*k,?_⟩
    change D F ((n:F)⁻¹*k) = a-b
    rw [map_mul,hk,mul_sub]
    exact congrArg₂ (·-·) (hcancel a) (hcancel b)
  · intro x
    obtain ⟨a,rfl⟩ := QuotientAddGroup.mk'_surjective (P F) x
    refine ⟨m (r*a),?_⟩
    change n • m (r*a)=m a
    rw [←map_nsmul]
    congr 1
    rw [nsmul_eq_mul,mul_left_comm,←nsmul_eq_mul,hcancel]

private theorem integral_iff (ξ : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), (D F ξ).2 v ∈ v.adicCompletionIntegers F) ↔
      ξ ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one F ξ
    intro v
    have hx := h v
    change ((ξ : v.adicCompletion F)) ∈ v.adicCompletionIntegers F at hx
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers,HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hx
  · rintro ⟨a,rfl⟩ v
    exact AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a
end AdeleClassProof
open AdeleClassProof


open NumberField IsDedekindDomain

theorem solution (F : Type*) [Field F] [NumberField F] :
    (∀ A : Set F, IsClosed (algebraMap F (AdeleRing (𝓞 F) F) '' A)) ∧
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F) ∧
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ∧
    T2Space (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ∧
    (∀ n : ℕ, 0 < n → Function.Bijective
      (fun x : AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F => n • x)) ∧
    (∀ x : AdeleRing (𝓞 F) F, ∃ y : AdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F), y.2 v ∈ v.adicCompletionIntegers F) ∧
      ∃ ξ : F, x = y + algebraMap F (AdeleRing (𝓞 F) F) ξ) ∧
    (∀ ξ : F, (∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 v ∈ v.adicCompletionIntegers F) ↔
      ξ ∈ (algebraMap (𝓞 F) F).range) ∧
    (∀ U : Set (AdeleRing (𝓞 F) F), IsOpen U → IsOpen
      ((QuotientAddGroup.mk :
          AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) ''
        (U ∩ {y | ∀ v : HeightOneSpectrum (𝓞 F), y.2 v ∈ v.adicCompletionIntegers F})))  := by
  letI hd : DiscreteTopology (P F) := principal_discrete F
  have hcl : IsClosed (P F : Set (A F)) := AddSubgroup.isClosed_of_discrete
  refine ⟨?_,hd,quotient_compact F,inferInstance,quotient_division F,?_,integral_iff F,?_⟩
  · intro S
    exact isClosed_of_subset_discrete_closed (fun _ h => by obtain ⟨r,_,rfl⟩ := h; exact ⟨r,rfl⟩)
      (isDiscrete_iff_discreteTopology.mpr hd) hcl
  · intro x
    obtain ⟨k,hk⟩ := AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x.2
    refine ⟨D F k+x,hk,-k,?_⟩
    rw [map_neg]; abel
  · intro U hU
    apply QuotientAddGroup.isOpenMap_coe _ (hU.inter ?_)
    exact (AdelicBox.isOpen_integralFiniteAdeles F).preimage continuous_snd



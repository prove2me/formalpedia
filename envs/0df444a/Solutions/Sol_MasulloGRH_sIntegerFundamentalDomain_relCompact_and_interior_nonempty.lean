-- Prove2me | solution 1 for MasulloGRH.sIntegerFundamentalDomain_relCompact_and_interior_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:46:20.660778+00:00
-- url     : https://prove2.me/submissions/6a5a6624-436c-4a65-be8a-41e89416f36c

import Mathlib
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_sIntegerFundamentalDomain_relCompact_and_interior_nonempty

open Filter IsLocalRing Topology
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

/-- The residue field of a completion at a height-one prime is isomorphic to the quotient
of the ring of integers by that prime. -/
theorem nonempty_residueFieldEquiv_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers F)) := by
  let O := v.adicCompletionIntegers F
  let f := (residue O).comp (algebraMap (𝓞 F) O)
  let q : 𝓞 F ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < (1 : ℤᵐ⁰)
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v r
    exact h.trans_lt ((v.valuation_lt_one_iff_mem r).2 hr))
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  -- Approximate the representative first by an element of `F`, then by one of `𝓞 F`.
  let ν : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion F)) < 1} ∈ 𝓝 (x : v.adicCompletion F) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  change ν (algebraMap F (v.adicCompletion F) a - x) < 1 at ha
  have ha' : v.valuation F a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap F (v.adicCompletion F) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap (𝓞 F) (v.adicCompletion F) r - algebraMap F (v.adicCompletion F) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v (((algebraMap (𝓞 F) F) r - a : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap (𝓞 F) O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap (𝓞 F) (v.adicCompletion F) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

/-- The residue field of the completion at a height-one prime is finite. -/
theorem finite_residueField_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Finite (ResidueField (v.adicCompletionIntegers F)) := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv_adicCompletion (F := F) v
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact Finite.of_equiv _ e.toEquiv

/-- The ring of integers of the completion at a height-one prime is compact. -/
theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hclosed : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers F) := hclosed.completeSpace_coe
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
      ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        finite_residueField_adicCompletion v⟩)

end Sol_MasulloGRH_sIntegerFundamentalDomain_relCompact_and_interior_nonempty

open MasulloGRH
open Sol_MasulloGRH_sIntegerFundamentalDomain_relCompact_and_interior_nonempty

theorem solution
    (F : Type*) [Field F] [NumberField F] {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (closure (sIntegerFundamentalDomain F b Sf)) ∧
    (interior (sIntegerFundamentalDomain F b Sf)).Nonempty := by
  classical
  let j := ((mixedEmbedding F).comp (algebraMap (𝓞 F) F)).toIntAlgHom.toLinearMap
  let e := LinearEquiv.ofInjective j ((mixedEmbedding_injective F).comp RingOfIntegers.coe_injective)
  let B := (b.map e).ofZLatticeBasis ℝ (mixedEmbedding.integerLattice F)
  let : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  -- the archimedean domain is the pull-back of the half-open parallelepiped of `B`
  have hD : ∀ x : InfiniteAdeleRing F,
      x ∈ RiemannMasullo.infiniteAdeleFundamentalDomain F b ↔ m x ∈ ZSpan.fundamentalDomain B :=
    fun _ => Iff.rfl
  -- `m` is a homeomorphism
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans
      ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph).prodCongr
        ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  have hhm : ∀ x : InfiniteAdeleRing F, h x = m x := fun _ => rfl
  have hOc : ∀ v : Sf, IsCompact
      ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
        Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) :=
    fun v => isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F))
  refine ⟨?_, ?_⟩
  · -- relative compactness
    have hbox : IsCompact ((h.symm '' (B.parallelepiped : Set (mixedEmbedding.mixedSpace F))) ×ˢ
        Set.pi Set.univ (fun v : Sf ↦
          ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
            Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))) :=
      (B.parallelepiped.isCompact.image h.symm.continuous).prod
        (isCompact_univ_pi fun v ↦ hOc v)
    refine hbox.closure_of_subset ?_
    rintro x ⟨hx, hxv⟩
    refine ⟨⟨h x.1, ?_, h.symm_apply_apply _⟩, fun v _ ↦ hxv v⟩
    rw [hhm]
    exact ZSpan.fundamentalDomain_subset_parallelepiped B ((hD x.1).mp hx)
  · -- non-empty interior
    have hm : Continuous m := by
      have : (m : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) = h := rfl
      rw [this]
      exact h.continuous
    let coords : SAdeleRing F Sf → ι → ℝ := fun x ↦ B.equivFun (m x.1)
    let cube : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι ↦ Set.Ioo (0 : ℝ) 1)
    let box : Set ((v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :=
      Set.pi Set.univ (fun v : Sf ↦
          ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :
            Set ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))
    let U : Set (SAdeleRing F Sf) := (coords ⁻¹' cube) ∩ (Prod.snd ⁻¹' box)
    have hbox : IsOpen box :=
      isOpen_set_pi Set.finite_univ fun v _ ↦
        Valued.isOpen_valuationSubring ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    have hU : IsOpen U :=
      ((isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo).preimage
        ((continuous_equivFun_basis B).comp (hm.comp continuous_fst))).inter
        (hbox.preimage continuous_snd)
    let a : SAdeleRing F Sf := (m.symm (B.equivFun.symm fun _ ↦ 1 / 2), 0)
    refine ⟨a, mem_interior.mpr ⟨U, ?_, hU, ?_⟩⟩
    · rintro x ⟨hx, hInt⟩
      refine ⟨(hD x.1).mpr ((ZSpan.mem_fundamentalDomain B).mpr fun i ↦ ?_),
        fun v ↦ hInt v (Set.mem_univ v)⟩
      exact Set.Ioo_subset_Ico_self (hx i (Set.mem_univ i))
    · refine ⟨?_, ?_⟩
      · change B.equivFun (m (m.symm (B.equivFun.symm fun _ ↦ 1 / 2))) ∈ cube
        rw [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact fun _ _ ↦ ⟨by norm_num, by norm_num⟩
      · intro v _
        exact ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F).zero_mem

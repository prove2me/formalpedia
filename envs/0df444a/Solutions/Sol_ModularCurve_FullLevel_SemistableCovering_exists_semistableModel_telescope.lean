-- Prove2me | solution 1 for ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7857c2f9-d2e3-593a-b040-c3ed2b54ce0f

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope.AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing"

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place SemistableModel.localRing SemistableModel"
namespace SemistableModel
p2m_export "AlgebraicCurve.SemistableModel" "localRing Descent pt_mem_smoothLocus residue_mem_of_mem_localRing_sm exists_eq_mul_sm eq_of_sm_specializes gen_mem_smoothLocus localRing_nd classify_bijective exists_residue_eq_sm isProper flat gen pt_specializes_sm toBase locallyOfFinitePresentation sm eq_of_nd_specializes sm_mem_smoothLocus pt_specializes_nd toBase_pt isIntegral nd_not_mem_smoothLocus toBase_gen eq_of_gen_specializes exists_residue_eq_nd X nd exists_eq_mul_nd ffEquiv eq_of_pt_specializes localRing_sm localRing_pt ffEquiv_algebraMap gen_specializes_nd gen_specializes_sm residue_nd pt localRing_gen"
namespace TeleReindex
p2m_open "AlgebraicCurve.SemistableModel AlgebraicCurve"

open CategoryTheory AlgebraicGeometry

universe u v w u₁ u₂ u₃ u₄

variable {L : Type u} [Field L] {A : ValuationSubring L}
variable {F : Type v} [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} {Fbar : ιV → Type w} [∀ i, Field (Fbar i)]
  [∀ i, Algebra (ResidueField A) (Fbar i)]
variable {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
variable {N : ∀ j, ιE → Place (ResidueField A) (Fbar j)}
variable {ιV' : Type u₃} {ιE' : Type u₄}

def reindexN
    (M : SemistableModel A F Fbar C An src tgt (fun e => N (src e) e) (fun e => N (tgt e) e))
    (eV : ιV' ≃ ιV) (eE : ιE' ≃ ιE) :
    SemistableModel A F (fun i' => Fbar (eV i')) (fun i' => C (eV i')) (fun e' => An (eE e'))
      (fun e' => eV.symm (src (eE e'))) (fun e' => eV.symm (tgt (eE e')))
      (fun e' => N (eV (eV.symm (src (eE e')))) (eE e')) (fun e' => N (eV (eV.symm (tgt (eE e')))) (eE e')) := by
  classical

  have T1 : ∀ (Φ : ιV → Prop) (e' : ιE'), Φ (src (eE e')) → Φ (eV (eV.symm (src (eE e')))) :=
    fun Φ e' h => by rw [Equiv.apply_symm_apply]; exact h
  have T2 : ∀ (Φ : ιV → ιV → Prop) (e' : ιE'), Φ (src (eE e')) (tgt (eE e')) →
      Φ (eV (eV.symm (src (eE e')))) (eV (eV.symm (tgt (eE e')))) :=
    fun Φ e' h => by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact h
  refine
    { X := M.X
      toBase := M.toBase
      isIntegral := M.isIntegral
      isProper := M.isProper
      flat := M.flat
      locallyOfFinitePresentation := M.locallyOfFinitePresentation
      ffEquiv := M.ffEquiv
      ffEquiv_algebraMap := M.ffEquiv_algebraMap
      pt := M.pt
      localRing_pt := M.localRing_pt
      toBase_pt := M.toBase_pt
      gen := fun i' => M.gen (eV i')
      localRing_gen := fun i' => M.localRing_gen (eV i')
      toBase_gen := fun i' => M.toBase_gen (eV i')
      sm := fun i' Q => M.sm (eV i') Q
      nd := fun e' => M.nd (eE e')
      classify_bijective := ?_
      pt_specializes_sm := fun i' P hP => M.pt_specializes_sm (eV i') P hP
      pt_specializes_nd := fun e' P hP => M.pt_specializes_nd (eE e') P hP
      eq_of_pt_specializes := ?_
      gen_specializes_sm := fun i' Q => M.gen_specializes_sm (eV i') Q
      gen_specializes_nd := fun e' =>
        T2 (fun a b => M.gen a ⤳ M.nd (eE e') ∧ M.gen b ⤳ M.nd (eE e')) e' (M.gen_specializes_nd (eE e'))
      eq_of_gen_specializes := ?_
      eq_of_sm_specializes := fun i' Q x h => M.eq_of_sm_specializes (eV i') Q x h
      eq_of_nd_specializes := fun e' x h => M.eq_of_nd_specializes (eE e') x h
      localRing_sm := fun i' Q f => M.localRing_sm (eV i') Q f
      localRing_nd := fun e' f =>
        T2 (fun a b => f ∈ SemistableModel.localRing M.X M.ffEquiv (M.nd (eE e')) ↔
          (f ∈ (C a).integers ∧ f ∈ (C b).integers ∧ ∀ P ∈ (An (eE e')).dom, f ∈ P.toValuationSubring)) e'
          (M.localRing_nd (eE e') f)
      residue_mem_of_mem_localRing_sm := fun i' Q f hf h => M.residue_mem_of_mem_localRing_sm (eV i') Q f hf h
      exists_residue_eq_sm := fun i' Q g hg => M.exists_residue_eq_sm (eV i') Q g hg
      exists_eq_mul_sm := fun i' Q f hf h h0 => M.exists_eq_mul_sm (eV i') Q f hf h h0
      residue_nd := fun e' =>
        T2 (fun a b => ∀ (f : F) (hs : f ∈ (C a).integers) (ht : f ∈ (C b).integers),
          f ∈ SemistableModel.localRing M.X M.ffEquiv (M.nd (eE e')) →
            ∃ (h1 : (C a).residue ⟨f, hs⟩ ∈ (N a (eE e')).toValuationSubring)
              (h2 : (C b).residue ⟨f, ht⟩ ∈ (N b (eE e')).toValuationSubring) (c : ResidueField A),
              IsLocalRing.residue (N a (eE e')).toValuationSubring ⟨_, h1⟩ =
                  algebraMap (ResidueField A) (N a (eE e')).ResidueField c ∧
              IsLocalRing.residue (N b (eE e')).toValuationSubring ⟨_, h2⟩ =
                  algebraMap (ResidueField A) (N b (eE e')).ResidueField c) e' (M.residue_nd (eE e'))
      exists_residue_eq_nd := ?_
      exists_eq_mul_nd := fun e' =>
        T2 (fun a b => ∀ (f : F) (hs : f ∈ (C a).integers) (ht : f ∈ (C b).integers),
          f ∈ SemistableModel.localRing M.X M.ffEquiv (M.nd (eE e')) →
            (C a).residue ⟨f, hs⟩ = 0 → (C b).residue ⟨f, ht⟩ = 0 →
              ∃ a' ∈ maximalIdeal A, ∃ g ∈ SemistableModel.localRing M.X M.ffEquiv (M.nd (eE e')),
                f = algebraMap L F (a' : L) * g) e' (M.exists_eq_mul_nd (eE e'))
      pt_mem_smoothLocus := M.pt_mem_smoothLocus
      gen_mem_smoothLocus := fun i' => M.gen_mem_smoothLocus (eV i')
      sm_mem_smoothLocus := fun i' Q => M.sm_mem_smoothLocus (eV i') Q
      nd_not_mem_smoothLocus := fun e' => M.nd_not_mem_smoothLocus (eE e') }
  ·
    let E : Unit ⊕ (Place L F ⊕ (ιV' ⊕ ((Σ i' : ιV', {Q : Place (ResidueField A) (Fbar (eV i')) // Q ∉ (C (eV i')).nodes}) ⊕ ιE'))) ≃
        Unit ⊕ (Place L F ⊕ (ιV ⊕ ((Σ i : ιV, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) ⊕ ιE))) :=
      Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr eV
        (Equiv.sumCongr (Equiv.sigmaCongrLeft (β := fun i => {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) eV) eE)))
    have hcomp : (Sum.elim (fun _ : Unit => genericPoint M.X)
        (Sum.elim M.pt (Sum.elim (fun i' => M.gen (eV i')) (Sum.elim
          (fun iQ : (Σ i' : ιV', {Q : Place (ResidueField A) (Fbar (eV i')) // Q ∉ (C (eV i')).nodes}) => M.sm (eV iQ.1) iQ.2)
          (fun e' => M.nd (eE e')))))) =
      (Sum.elim (fun _ : Unit => genericPoint M.X)
        (Sum.elim M.pt (Sum.elim M.gen (Sum.elim
          (fun iQ : (Σ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) => M.sm iQ.1 iQ.2) M.nd)))) ∘ E := by
      funext x
      rcases x with u | P | i' | iQ | e' <;> rfl
    rw [hcomp]
    exact M.classify_bijective.comp E.bijective
  ·
    intro P x h
    rcases M.eq_of_pt_specializes P x h with h1 | ⟨i, hP, hx⟩ | ⟨e, he, hx⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ⟨eV.symm i, ?_⟩)
      show (fun j => ∃ hP : P ∈ (C j).dom, x = M.sm j ⟨(C j).placeMap P, (C j).placeMap_not_mem_nodes P hP⟩)
        (eV (eV.symm i))
      rw [Equiv.apply_symm_apply]
      exact ⟨hP, hx⟩
    · exact Or.inr (Or.inr ⟨eE.symm e, by rw [Equiv.apply_symm_apply]; exact he, by rw [Equiv.apply_symm_apply]; exact hx⟩)
  ·
    intro j' x h
    rcases M.eq_of_gen_specializes (eV j') x h with h1 | ⟨Q, hQ⟩ | ⟨e, he, hx⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨Q, hQ⟩)
    · refine Or.inr (Or.inr ⟨eE.symm e, ?_, by rw [Equiv.apply_symm_apply]; exact hx⟩)
      rw [Equiv.apply_symm_apply]
      rcases he with he | he
      · exact Or.inl (by rw [he, Equiv.symm_apply_apply])
      · exact Or.inr (by rw [he, Equiv.symm_apply_apply])
  ·
    intro e' g'
    obtain ⟨g, rfl⟩ := (Equiv.piCongrLeft' Fbar eV.symm).surjective g'
    exact T2 (fun a b => ∀ (h1 : g a ∈ (N a (eE e')).toValuationSubring)
        (h2 : g b ∈ (N b (eE e')).toValuationSubring) (c : ResidueField A),
        IsLocalRing.residue (N a (eE e')).toValuationSubring ⟨_, h1⟩ =
            algebraMap (ResidueField A) (N a (eE e')).ResidueField c →
        IsLocalRing.residue (N b (eE e')).toValuationSubring ⟨_, h2⟩ =
            algebraMap (ResidueField A) (N b (eE e')).ResidueField c →
          ∃ (f : F) (hs : f ∈ (C a).integers) (ht : f ∈ (C b).integers),
            f ∈ SemistableModel.localRing M.X M.ffEquiv (M.nd (eE e')) ∧
            (C a).residue ⟨f, hs⟩ = g a ∧ (C b).residue ⟨f, ht⟩ = g b) e' (M.exists_residue_eq_nd (eE e') g)

end AlgebraicCurve.SemistableModel.TeleReindex

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place SemistableModel.localRing SemistableModel"
namespace SemistableModel
p2m_export "AlgebraicCurve.SemistableModel" "localRing Descent pt_mem_smoothLocus residue_mem_of_mem_localRing_sm exists_eq_mul_sm eq_of_sm_specializes gen_mem_smoothLocus localRing_nd classify_bijective exists_residue_eq_sm isProper flat gen pt_specializes_sm toBase locallyOfFinitePresentation sm eq_of_nd_specializes sm_mem_smoothLocus pt_specializes_nd toBase_pt isIntegral nd_not_mem_smoothLocus toBase_gen eq_of_gen_specializes exists_residue_eq_nd X nd exists_eq_mul_nd ffEquiv eq_of_pt_specializes localRing_sm localRing_pt ffEquiv_algebraMap gen_specializes_nd gen_specializes_sm residue_nd pt localRing_gen"
namespace TeleReindex
p2m_open "AlgebraicCurve.SemistableModel AlgebraicCurve"

universe u v w u₁ u₂ u₃ u₄
variable {L : Type u} [Field L] {A : ValuationSubring L}
variable {F : Type v} [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} {Fbar : ιV → Type w} [∀ i, Field (Fbar i)]
  [∀ i, Algebra (ResidueField A) (Fbar i)]
variable {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
variable {N : ∀ j, ιE → Place (ResidueField A) (Fbar j)}
variable {ιV' : Type u₃} {ιE' : Type u₄}

def descentReindexN
    {M : SemistableModel A F Fbar C An src tgt (fun e => N (src e) e) (fun e => N (tgt e) e)}
    (D : M.Descent) (eV : ιV' ≃ ιV) (eE : ιE' ≃ ιE) : (reindexN M eV eE).Descent where
  A₀ := D.A₀
  ι := D.ι
  ι_injective := D.ι_injective
  K₀ := D.K₀
  range_ι := D.range_ι
  residue_comp_surjective := D.residue_comp_surjective
  X₀ := D.X₀
  toBase₀ := D.toBase₀
  iso := D.iso
  iso_snd := D.iso_snd
  base_genericPoint := D.base_genericPoint
  F₀ := D.F₀
  ffEquiv₀ := D.ffEquiv₀
  ffEquiv₀_ffEquiv := D.ffEquiv₀_ffEquiv

end AlgebraicCurve.SemistableModel.TeleReindex

theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W)
    (M : AlgebraicCurve.SemistableModel A ↥(fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
      (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
      (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
      (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
    (D : M.Descent) :
    ∃ (M₁ : AlgebraicCurve.SemistableModel A ↥(fieldBar q M') 𝒞.teleFbar 𝒞.teleChart 𝒞.teleAn 𝒞.teleSrc 𝒞.teleTgt
        𝒞.teleXs 𝒞.teleXt) (D₁ : M₁.Descent), M₁.X = M.X := by
  exact ⟨AlgebraicCurve.SemistableModel.TeleReindex.reindexN M 𝒞.eIdx.symm 𝒞.eEdge.symm,
    AlgebraicCurve.SemistableModel.TeleReindex.descentReindexN D 𝒞.eIdx.symm 𝒞.eEdge.symm, rfl⟩

end S_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope
end P2MW
export P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope (solution)

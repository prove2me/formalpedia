-- Prove2me | solution 1 for ModularCurve.FullLevel.SemistableCovering.telescope_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3dbcd602-d799-5c3c-9176-f90d37879c1b

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws.ModularCurve.FullLevel IsLocalRing"

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.SemistableCovering instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "SemistableCovering fieldBar SemistableCovering.GenusClause SemistableCovering.HasDiscFibres"
namespace SemistableCovering
p2m_export "ModularCurve.FullLevel.SemistableCovering" "sumFbar sumChart sumNode teleN teleM eIdx eEdge teleFbar instHasPrincipalDivisorsTeleFbar isRational_teleFbar teleChart teleAn teleAn' teleWidth teleWidth_spec teleSrc teleTgt teleXs teleXt teleChart_eIdx_iff CIg isAttached param_mul existsUnique_xs_eq modulus_ne_zero dom_eq CSS FSS partition An An' mk modulus_eq existsUnique_xt_eq FIg WidthClause GenusClause HasDiscFibres DiscFibreClause CurveClause"
namespace TeleLaws
p2m_open "ModularCurve.FullLevel.SemistableCovering ModularCurve.FullLevel ModularCurve"

p2m_open "ModularCurve.FullLevel.SemistableCovering P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws.ModularCurve.FullLevel.SemistableCovering"

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
variable (𝒞 : SemistableCovering q M' A W)

private theorem isCurveOver_Fb (hC : 𝒞.CurveClause) : ∀ j, IsCurveOver (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => (hC.1 ℓ).1
  | .inr s => (hC.2 s).1

private theorem essFiniteType_Fb (hC : 𝒞.CurveClause) : ∀ j, Algebra.EssFiniteType (ResidueField A) (𝒞.sumFbar j)
  | .inl ℓ => (hC.1 ℓ).2
  | .inr s => (hC.2 s).2

private theorem hasDiscFibres_chart (hD : 𝒞.DiscFibreClause) : ∀ j, SemistableCovering.HasDiscFibres (𝒞.sumChart j)
  | .inl ℓ => hD.1 ℓ
  | .inr s => hD.2 s

section reindex

variable {n m : ℕ} (eι : CuspidalType.ProjLine q ⊕ ↥W ≃ Fin n) (eE : CuspidalType.ProjLine q × ↥W ≃ Fin m)

private theorem isAttached_reindex (e : Fin m) :
    (𝒞.An (eE.symm e).1 (eE.symm e).2).IsAttached (𝒞.sumChart (eι.symm (eι (Sum.inl (eE.symm e).1))))
        (𝒞.sumNode (eι.symm (eι (Sum.inl (eE.symm e).1))) (eE.symm e)) ∧
      (𝒞.An' (eE.symm e).1 (eE.symm e).2).IsAttached (𝒞.sumChart (eι.symm (eι (Sum.inr (eE.symm e).2))))
        (𝒞.sumNode (eι.symm (eι (Sum.inr (eE.symm e).2))) (eE.symm e)) := by
  have key : ∀ j (p : CuspidalType.ProjLine q × ↥W),
      (j = Sum.inl p.1 → (𝒞.An p.1 p.2).IsAttached (𝒞.sumChart j) (𝒞.sumNode j p)) ∧
      (j = Sum.inr p.2 → (𝒞.An' p.1 p.2).IsAttached (𝒞.sumChart j) (𝒞.sumNode j p)) := by
    intro j p
    constructor
    · rintro rfl; exact (𝒞.isAttached p.1 p.2).1
    · rintro rfl; exact (𝒞.isAttached p.1 p.2).2
  exact ⟨(key _ _).1 (eι.symm_apply_apply _), (key _ _).2 (eι.symm_apply_apply _)⟩

private theorem sigma_mk_eq_iff (i : Fin n) (x : Place (ResidueField ↥A) (𝒞.sumFbar (eι.symm i)))
    (a : CuspidalType.ProjLine q ⊕ ↥W) (p : CuspidalType.ProjLine q × ↥W) :
    ((⟨eι a, 𝒞.sumNode (eι.symm (eι a)) p⟩ : Σ j : Fin n, Place (ResidueField ↥A) (𝒞.sumFbar (eι.symm j))) = ⟨i, x⟩) ↔
      (a = eι.symm i ∧ 𝒞.sumNode (eι.symm i) p = x) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
    subst h1
    exact ⟨(eι.symm_apply_apply a).symm, eq_of_heq h2⟩
  · rintro ⟨h1, h2⟩
    subst h1
    have key : ∀ k : Fin n, k = i →
        ((⟨k, 𝒞.sumNode (eι.symm k) p⟩ : Σ j : Fin n, Place (ResidueField ↥A) (𝒞.sumFbar (eι.symm j))) = ⟨i, x⟩) := by
      rintro k rfl; exact congrArg _ h2
    exact key _ (eι.apply_symm_apply i)

private theorem existsUnique_end (j : CuspidalType.ProjLine q ⊕ ↥W) (y : Place (ResidueField ↥A) (𝒞.sumFbar j))
    (hy : y ∈ (𝒞.sumChart j).nodes) :
    ∃! e : Fin m, (Sum.inl (eE.symm e).1 = j ∧ 𝒞.sumNode j (eE.symm e) = y) ∨
      (Sum.inr (eE.symm e).2 = j ∧ 𝒞.sumNode j (eE.symm e) = y) := by
  revert y
  cases j with
  | inl ℓ =>
    intro y hy
    obtain ⟨s, hs, hu⟩ := 𝒞.existsUnique_xs_eq ℓ y hy
    refine ⟨eE (ℓ, s), Or.inl ⟨by simp only [Equiv.symm_apply_apply], by simp only [Equiv.symm_apply_apply]; exact hs⟩, ?_⟩
    rintro e (⟨h1, h2⟩ | ⟨h1, -⟩)
    · have h3 : (eE.symm e).2 = s := hu _ h2
      rw [← eE.apply_symm_apply e, @Prod.ext _ _ (eE.symm e) (ℓ, s) (Sum.inl_injective h1) h3]
    · exact absurd h1 Sum.inr_ne_inl
  | inr s =>
    intro y hy
    obtain ⟨ℓ, hℓ, hu⟩ := 𝒞.existsUnique_xt_eq s y hy
    refine ⟨eE (ℓ, s), Or.inr ⟨by simp only [Equiv.symm_apply_apply], by simp only [Equiv.symm_apply_apply]; exact hℓ⟩, ?_⟩
    rintro e (⟨h1, -⟩ | ⟨h1, h2⟩)
    · exact absurd h1 Sum.inl_ne_inr
    · have h3 : (eE.symm e).1 = ℓ := hu _ h2
      rw [← eE.apply_symm_apply e, @Prod.ext _ _ (eE.symm e) (ℓ, s) h3 (Sum.inr_injective h1)]

private theorem existsUnique_end_reindex (i : Fin n) (x : Place (ResidueField ↥A) (𝒞.sumFbar (eι.symm i)))
    (hx : x ∈ (𝒞.sumChart (eι.symm i)).nodes) :
    ∃! e : Fin m,
      ((⟨eι (Sum.inl (eE.symm e).1), 𝒞.sumNode (eι.symm (eι (Sum.inl (eE.symm e).1))) (eE.symm e)⟩ :
          Σ j : Fin n, Place (ResidueField ↥A) (𝒞.sumFbar (eι.symm j))) = ⟨i, x⟩ ∨
      (⟨eι (Sum.inr (eE.symm e).2), 𝒞.sumNode (eι.symm (eι (Sum.inr (eE.symm e).2))) (eE.symm e)⟩ :
          Σ j : Fin n, Place (ResidueField ↥A) (𝒞.sumFbar (eι.symm j))) = ⟨i, x⟩) :=
  (existsUnique_congr fun _ =>
      or_congr (sigma_mk_eq_iff 𝒞 eι i x _ _) (sigma_mk_eq_iff 𝒞 eι i x _ _)).2
    (existsUnique_end 𝒞 eE _ x hx)

private theorem partition_reindex (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) :
    (∃ i : Fin n, P ∈ (𝒞.sumChart (eι.symm i)).dom ∧ (∀ j : Fin n, P ∈ (𝒞.sumChart (eι.symm j)).dom → j = i) ∧
        ∀ e : Fin m, P ∉ (𝒞.An (eE.symm e).1 (eE.symm e).2).dom) ∨
      (∃ e : Fin m, P ∈ (𝒞.An (eE.symm e).1 (eE.symm e).2).dom ∧
        (∀ e' : Fin m, P ∈ (𝒞.An (eE.symm e').1 (eE.symm e').2).dom → e' = e) ∧
        ∀ i : Fin n, P ∉ (𝒞.sumChart (eι.symm i)).dom) := by
  have key : ∀ j, P ∈ (𝒞.sumChart j).dom ↔
      (∃ ℓ, j = Sum.inl ℓ ∧ P ∈ (𝒞.CIg ℓ).dom) ∨ (∃ s, j = Sum.inr s ∧ P ∈ (𝒞.CSS s).dom) := by
    rintro (ℓ | s)
    · simp only [sumChart, Sum.inl.injEq, exists_eq_left', reduceCtorEq, false_and, exists_false, or_false]
    · simp only [sumChart, reduceCtorEq, false_and, exists_false, Sum.inr.injEq, exists_eq_left', false_or]
  rcases 𝒞.partition P with ⟨ℓ, hP, huI, hnS, hnA⟩ | ⟨s, hP, huS, hnI, hnA⟩ | ⟨ℓ, s, hP, hu, hnI, hnS⟩
  · refine Or.inl ⟨eι (Sum.inl ℓ), ?_, ?_, fun e => hnA _ _⟩
    · exact (key _).2 (Or.inl ⟨ℓ, eι.symm_apply_apply _, hP⟩)
    · intro i hi
      rcases (key _).1 hi with ⟨ℓ', h1, h2⟩ | ⟨s', -, h2⟩
      · rw [huI ℓ' h2] at h1
        exact (eι.symm_apply_eq).1 h1
      · exact absurd h2 (hnS s')
  · refine Or.inl ⟨eι (Sum.inr s), ?_, ?_, fun e => hnA _ _⟩
    · exact (key _).2 (Or.inr ⟨s, eι.symm_apply_apply _, hP⟩)
    · intro i hi
      rcases (key _).1 hi with ⟨ℓ', -, h2⟩ | ⟨s', h1, h2⟩
      · exact absurd h2 (hnI ℓ')
      · rw [huS s' h2] at h1
        exact (eι.symm_apply_eq).1 h1
  · refine Or.inr ⟨eE (ℓ, s), by simp only [Equiv.symm_apply_apply]; exact hP, ?_, ?_⟩
    · intro e' he'
      obtain ⟨h1, h2⟩ := hu _ _ he'
      rw [← eE.apply_symm_apply e', @Prod.ext _ _ (eE.symm e') (ℓ, s) h1 h2]
    · intro i hi
      rcases (key _).1 hi with ⟨ℓ', -, h2⟩ | ⟨s', -, h2⟩
      · exact hnI ℓ' h2
      · exact hnS s' h2

include eE in

private theorem genus_reindex (hG : 𝒞.GenusClause) :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + n =
      ∑ i : Fin n, AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.sumFbar (eι.symm i)) + m + 1 := by
  letI : Fintype (CuspidalType.ProjLine q) := Fintype.ofFinite _
  have hn : n = Nat.card (CuspidalType.ProjLine q) + W.card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe W, ← Fintype.card_sum, Fintype.card_congr eι, Fintype.card_fin]
  have hm : m = Nat.card (CuspidalType.ProjLine q) * W.card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe W, ← Fintype.card_prod, Fintype.card_congr eE, Fintype.card_fin]
  have hsum : ∑ i : Fin n, AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.sumFbar (eι.symm i)) =
      ∑ᶠ ℓ : CuspidalType.ProjLine q, AlgebraicCurve.genusFF (ResidueField A) (𝒞.FIg ℓ) +
        ∑ s ∈ W.attach, AlgebraicCurve.genusFF (ResidueField A) (𝒞.FSS s) := by
    rw [Fintype.sum_equiv eι.symm (fun i => AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.sumFbar (eι.symm i)))
      (fun j => AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.sumFbar j)) (fun _ => rfl), Fintype.sum_sum_type,
      finsum_eq_sum_of_fintype, ← Finset.univ_eq_attach]
    rfl
  have hG' := hG
  unfold SemistableCovering.GenusClause at hG'
  rw [hsum]
  omega

end reindex

end ModularCurve.FullLevel.SemistableCovering.TeleLaws

open _root_.ModularCurve.FullLevel.SemistableCovering _root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws.ModularCurve.FullLevel.SemistableCovering in

theorem solution
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W) (π : A) (hWd : 𝒞.WidthClause π)
    (hG : 𝒞.GenusClause) (hD : 𝒞.DiscFibreClause) (hC : 𝒞.CurveClause) :
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(fieldBar q M') + 𝒞.teleN =
        ∑ i : Fin 𝒞.teleN, AlgebraicCurve.genusFF (ResidueField ↥A) (𝒞.teleFbar i) + 𝒞.teleM + 1 ∧
      (∀ i, IsCurveOver (ResidueField ↥A) (𝒞.teleFbar i)) ∧ (∀ i, Algebra.EssFiniteType (ResidueField ↥A) (𝒞.teleFbar i)) ∧
      (∀ i, ∀ Q : Place (ResidueField ↥A) (𝒞.teleFbar i), Q ∉ (𝒞.teleChart i).nodes →
        ∃ (T : ↥(fieldBar q M')) (hT : T ∈ (𝒞.teleChart i).integers),
          (𝒞.teleChart i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((𝒞.teleChart i).residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ (𝒞.teleChart i).dom, (𝒞.teleChart i).placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ (𝒞.teleChart i).dom ∧ (𝒞.teleChart i).placeMap P = Q ∧ P.evalAt T = c) ∧
      (∀ e, 1 ≤ 𝒞.teleWidth π e ∧ ∃ u : Aˣ, (𝒞.teleAn e).modulus = u * π ^ 𝒞.teleWidth π e) ∧
      (∀ i, HasPrincipalDivisors (ResidueField ↥A) (𝒞.teleFbar i)) ∧
      (∀ i (Q : Place (ResidueField ↥A) (𝒞.teleFbar i)), Q.IsRational) ∧
      (∀ e, (𝒞.teleAn' e).dom = (𝒞.teleAn e).dom ∧ (𝒞.teleAn' e).modulus = (𝒞.teleAn e).modulus ∧
        ((𝒞.teleAn e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (𝒞.teleAn' e).param * (𝒞.teleAn e).param
          = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((𝒞.teleAn e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (𝒞.teleAn e).IsAttached (𝒞.teleChart (𝒞.teleSrc e)) (𝒞.teleXs e) ∧ (𝒞.teleAn' e).IsAttached (𝒞.teleChart (𝒞.teleTgt e)) (𝒞.teleXt e)) ∧
      (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∃! e,
        (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (ResidueField ↥A) (𝒞.teleFbar j)) = ⟨i, x⟩ ∨
        (⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ : Σ j, Place (ResidueField ↥A) (𝒞.teleFbar j)) = ⟨i, x⟩) ∧
      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
        (∃ i, P ∈ (𝒞.teleChart i).dom ∧ (∀ j, P ∈ (𝒞.teleChart j).dom → j = i) ∧ ∀ e, P ∉ (𝒞.teleAn e).dom) ∨
        (∃ e, P ∈ (𝒞.teleAn e).dom ∧ (∀ e', P ∈ (𝒞.teleAn e').dom → e' = e) ∧ ∀ i, P ∉ (𝒞.teleChart i).dom)) := by
  classical
  exact ⟨TeleLaws.genus_reindex 𝒞 𝒞.eIdx 𝒞.eEdge hG,
    fun i => TeleLaws.isCurveOver_Fb 𝒞 hC (𝒞.eIdx.symm i), fun i => TeleLaws.essFiniteType_Fb 𝒞 hC (𝒞.eIdx.symm i),
    fun i => TeleLaws.hasDiscFibres_chart 𝒞 hD (𝒞.eIdx.symm i),
    fun e => 𝒞.teleWidth_spec π e (hWd (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2),
    fun i => 𝒞.instHasPrincipalDivisorsTeleFbar i, fun i Q => 𝒞.isRational_teleFbar i Q,
    fun e => ⟨𝒞.dom_eq _ _, 𝒞.modulus_eq _ _, 𝒞.modulus_ne_zero _ _, 𝒞.param_mul _ _⟩,
    TeleLaws.isAttached_reindex 𝒞 𝒞.eIdx 𝒞.eEdge, TeleLaws.existsUnique_end_reindex 𝒞 𝒞.eIdx 𝒞.eEdge,
    TeleLaws.partition_reindex 𝒞 𝒞.eIdx 𝒞.eEdge⟩

end S_ModularCurve_FullLevel_SemistableCovering_telescope_laws
end P2MW
export P2MW.S_ModularCurve_FullLevel_SemistableCovering_telescope_laws (solution)

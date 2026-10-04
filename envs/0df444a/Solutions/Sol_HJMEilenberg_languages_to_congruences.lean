-- Prove2me | solution 1 for HJMEilenberg.languages_to_congruences
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T11:23:19.292733+00:00
-- url     : https://prove2.me/submissions/2fae9ebb-0e8c-4d45-8e17-08cccb69b59c

import Definitions.Def_HJMEilenberg_Formations
import Theorems.Thm_HJMEilenberg_syntactic_universal
import Theorems.Thm_HJMEilenberg_finiteIndex_filter
import Mathlib.Data.Fintype.Prod

open MSKleene
open HJMEilenberg

private def languageEmpty {S : Type} {sig : Signature S} {A : Algebra sig} :
    Language A := fun _ => ∅

private def languageUnion {S : Type} {sig : Signature S} {A : Algebra sig}
    (K N : Language A) : Language A := fun s => K s ∪ N s

private def languageInter {S : Type} {sig : Signature S} {A : Algebra sig}
    (K N : Language A) : Language A := fun s => K s ∩ N s

private theorem selected_empty {S : Type} {sig : Signature S}
    (L : RegularLanguageFormation sig) (X : SSet S) :
    languageEmpty ∈ L.languages X := by
  apply L.top_saturated X
  intro s x y hxy
  simp [languageEmpty]

private theorem selected_union {S : Type} {sig : Signature S}
    (L : RegularLanguageFormation sig) (X : SSet S)
    {K N : Language (freeAlgebra sig X)}
    (hK : K ∈ L.languages X) (hN : N ∈ L.languages X) :
    languageUnion K N ∈ L.languages X := by
  apply L.inter_saturated X hK hN
  intro s x y hxy
  exact or_congr
    ((syntactic_universal (freeAlgebra sig X) K).1 s x y hxy.1)
    ((syntactic_universal (freeAlgebra sig X) N).1 s x y hxy.2)

private theorem selected_inter {S : Type} {sig : Signature S}
    (L : RegularLanguageFormation sig) (X : SSet S)
    {K N : Language (freeAlgebra sig X)}
    (hK : K ∈ L.languages X) (hN : N ∈ L.languages X) :
    languageInter K N ∈ L.languages X := by
  apply L.inter_saturated X hK hN
  intro s x y hxy
  exact and_congr
    ((syntactic_universal (freeAlgebra sig X) K).1 s x y hxy.1)
    ((syntactic_universal (freeAlgebra sig X) N).1 s x y hxy.2)

private def languageFinUnion {S : Type} {sig : Signature S} {A : Algebra sig}
    {ι : Type} (I : Finset ι) (K : ι → Language A) : Language A :=
  fun s => {x | ∃ i, i ∈ I ∧ x ∈ K i s}

private theorem selected_finUnion {S : Type} {sig : Signature S}
    (L : RegularLanguageFormation sig) (X : SSet S)
    {ι : Type} (I : Finset ι) (K : ι → Language (freeAlgebra sig X))
    (hK : ∀ i ∈ I, K i ∈ L.languages X) :
    languageFinUnion I K ∈ L.languages X := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      have hEq : languageFinUnion (∅ : Finset ι) K = languageEmpty := by
        funext s
        ext x
        simp [languageFinUnion, languageEmpty]
      rw [hEq]
      exact selected_empty L X
  | @insert a I ha ih =>
      have haK : K a ∈ L.languages X := hK a (by simp)
      have hIK : languageFinUnion I K ∈ L.languages X :=
        ih (fun i hi => hK i (by simp [hi]))
      have hu := selected_union L X haK hIK
      have hEq : languageFinUnion (insert a I) K =
          languageUnion (K a) (languageFinUnion I K) := by
        funext s
        ext x
        simp [languageFinUnion, languageUnion, ha, or_assoc]
      rw [hEq]
      exact hu

private def quotientClassLanguage {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi : Congruence A)
    (q : Σ s, Quotient (Phi.setoid s)) : Language A :=
  fun s => {x | (⟨s, Quotient.mk'' x⟩ : Σ t, Quotient (Phi.setoid t)) = q}

private theorem quotientClass_saturated {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi : Congruence A)
    (q : Σ s, Quotient (Phi.setoid s)) :
    Saturated Phi (quotientClassLanguage Phi q) := by
  intro s x y hxy
  have hmk : (⟨s, Quotient.mk'' x⟩ : Σ t, Quotient (Phi.setoid t)) =
      ⟨s, Quotient.mk'' y⟩ :=
    (Sigma.mk.inj_iff).2 ⟨rfl, heq_of_eq (Quotient.sound hxy)⟩
  constructor
  · intro hx
    exact hmk.symm.trans hx
  · intro hy
    exact hmk.trans hy

private def interLeft' {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A) (s : S) :
    Quotient ((Congruence.inter Phi Psi).setoid s) → Quotient (Phi.setoid s) :=
  Quotient.map id (fun _ _ h => h.1)

private def interRight' {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A) (s : S) :
    Quotient ((Congruence.inter Phi Psi).setoid s) → Quotient (Psi.setoid s) :=
  Quotient.map id (fun _ _ h => h.2)

private def interEmbedding' {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A) :
    (Σ s, Quotient ((Congruence.inter Phi Psi).setoid s)) →
      (Σ s, Quotient (Phi.setoid s)) × (Σ s, Quotient (Psi.setoid s)) :=
  fun q =>
    (⟨q.1, interLeft' Phi Psi q.1 q.2⟩,
      ⟨q.1, interRight' Phi Psi q.1 q.2⟩)

private theorem interEmbedding'_injective {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi Psi : Congruence A) :
    Function.Injective (interEmbedding' Phi Psi) := by
  rintro ⟨s, q⟩ ⟨t, r⟩ h
  have hs : s = t := congrArg (fun z => z.1.1) h
  subst t
  have hLeft : (⟨s, interLeft' Phi Psi s q⟩ : Σ u, Quotient (Phi.setoid u)) =
      ⟨s, interLeft' Phi Psi s r⟩ := congrArg Prod.fst h
  have hRight : (⟨s, interRight' Phi Psi s q⟩ : Σ u, Quotient (Psi.setoid u)) =
      ⟨s, interRight' Phi Psi s r⟩ := congrArg Prod.snd h
  have hPhi : interLeft' Phi Psi s q = interLeft' Phi Psi s r :=
    eq_of_heq ((Sigma.mk.inj_iff.mp hLeft).2)
  have hPsi : interRight' Phi Psi s q = interRight' Phi Psi s r :=
    eq_of_heq ((Sigma.mk.inj_iff.mp hRight).2)
  refine (Sigma.mk.inj_iff).2 ⟨rfl, heq_of_eq ?_⟩
  revert hPhi hPsi
  refine Quotient.inductionOn q ?_
  intro x
  refine Quotient.inductionOn r ?_
  intro y hPhi hPsi
  exact Quotient.sound ⟨Quotient.exact hPhi, Quotient.exact hPsi⟩

private def intersectionAtom {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi Psi : Congruence A)
    (q : Σ s, Quotient ((Congruence.inter Phi Psi).setoid s)) : Language A :=
  languageInter
    (quotientClassLanguage Phi (interEmbedding' Phi Psi q).1)
    (quotientClassLanguage Psi (interEmbedding' Phi Psi q).2)

private theorem mem_intersectionAtom_iff {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi Psi : Congruence A)
    (q : Σ s, Quotient ((Congruence.inter Phi Psi).setoid s))
    (s : S) (x : A.carrier s) :
    x ∈ intersectionAtom Phi Psi q s ↔
      (⟨s, Quotient.mk'' x⟩ :
        Σ t, Quotient ((Congruence.inter Phi Psi).setoid t)) = q := by
  constructor
  · intro hx
    apply interEmbedding'_injective Phi Psi
    exact Prod.ext hx.1 hx.2
  · intro hx
    have h := congrArg (interEmbedding' Phi Psi) hx
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private def quotientMember {S : Type} {sig : Signature S} {A : Algebra sig}
    (Phi : Congruence A) (K : Language A) (hK : Saturated Phi K)
    (q : Σ s, Quotient (Phi.setoid s)) : Prop :=
  match q with
  | ⟨s, q⟩ => Quotient.lift (fun x => x ∈ K s)
      (fun x y hxy => propext (hK s x y hxy)) q

private theorem all_inter_saturated_selected {S : Type} [Finite S]
    {sig : Signature S} (L : RegularLanguageFormation sig) (X : SSet S)
    (Phi Psi : Congruence (freeAlgebra sig X))
    (hPhi : ∀ K, Saturated Phi K → K ∈ L.languages X)
    (hPsi : ∀ K, Saturated Psi K → K ∈ L.languages X)
    (hFinite : (Congruence.inter Phi Psi).FiniteIndex)
    (K : Language (freeAlgebra sig X))
    (hKSat : Saturated (Congruence.inter Phi Psi) K) : K ∈ L.languages X := by
  classical
  let Q := Σ s, Quotient ((Congruence.inter Phi Psi).setoid s)
  haveI : Finite Q := hFinite
  let I := {q : Q // quotientMember (Congruence.inter Phi Psi) K hKSat q}
  letI : Fintype I := Fintype.ofFinite I
  have hAtoms : ∀ i : I, intersectionAtom Phi Psi i.1 ∈ L.languages X := by
    intro i
    apply selected_inter L X
    · exact hPhi _ (quotientClass_saturated Phi _)
    · exact hPsi _ (quotientClass_saturated Psi _)
  have hUnion : languageFinUnion (Finset.univ : Finset I)
      (fun i => intersectionAtom Phi Psi i.1) ∈ L.languages X :=
    selected_finUnion L X Finset.univ _ (fun i _ => hAtoms i)
  have hEq : languageFinUnion (Finset.univ : Finset I)
      (fun i => intersectionAtom Phi Psi i.1) = K := by
    funext s
    ext x
    constructor
    · rintro ⟨i, hi, hxi⟩
      have hclass := (mem_intersectionAtom_iff Phi Psi i.1 s x).1 hxi
      have hiK := i.2
      rw [← hclass] at hiK
      exact hiK
    · intro hx
      let q : Q := ⟨s, Quotient.mk'' x⟩
      have hq : quotientMember (Congruence.inter Phi Psi) K hKSat q := hx
      let i : I := ⟨q, hq⟩
      exact ⟨i, Finset.mem_univ i,
        (mem_intersectionAtom_iff Phi Psi i.1 s x).2 rfl⟩
  rw [← hEq]
  exact hUnion

private def pullbackQuotientMap {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta : Congruence B) :
    (Σ s, Quotient ((Congruence.pullback f Theta).setoid s)) →
      (Σ s, Quotient (Theta.setoid s)) :=
  fun q => ⟨q.1, Quotient.map (f.toFun q.1) (fun _ _ h => h) q.2⟩

private theorem pullbackQuotientMap_injective {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta : Congruence B) :
    Function.Injective (pullbackQuotientMap f Theta) := by
  rintro ⟨s, q⟩ ⟨t, r⟩ h
  have hs : s = t := congrArg Sigma.fst h
  subst t
  have hq : Quotient.map (f.toFun s) (fun _ _ h => h) q =
      Quotient.map (f.toFun s) (fun _ _ h => h) r :=
    eq_of_heq ((Sigma.mk.inj_iff.mp h).2)
  refine (Sigma.mk.inj_iff).2 ⟨rfl, heq_of_eq ?_⟩
  revert hq
  refine Quotient.inductionOn q ?_
  intro x
  refine Quotient.inductionOn r ?_
  intro y hq
  change (Quotient.mk'' (f.toFun s x) : Quotient (Theta.setoid s)) =
    Quotient.mk'' (f.toFun s y) at hq
  have hTheta : Theta.Rel s (f.toFun s x) (f.toFun s y) :=
    Quotient.exact hq
  exact Quotient.sound hTheta

private theorem pullback_finiteIndex {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta : Congruence B)
    (hTheta : Theta.FiniteIndex) : (Congruence.pullback f Theta).FiniteIndex := by
  unfold Congruence.FiniteIndex SFinite at hTheta ⊢
  haveI : Finite (Σ s, Quotient (Theta.setoid s)) := hTheta
  exact Finite.of_injective (pullbackQuotientMap f Theta)
    (pullbackQuotientMap_injective f Theta)

private def imageSaturation {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta : Congruence B)
    (K : Language A) : Language B :=
  fun s => {y | ∃ x, x ∈ K s ∧ Theta.Rel s (f.toFun s x) y}

private theorem imageSaturation_saturated {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta : Congruence B)
    (K : Language A) : Saturated Theta (imageSaturation f Theta K) := by
  intro s y z hyz
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (Theta.setoid s).trans hxy hyz⟩
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, (Theta.setoid s).trans hxz ((Theta.setoid s).symm hyz)⟩

private theorem quotientEpi_mono {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta Psi : Congruence B)
    (hle : Theta ≤ Psi) (hEpi : IsQuotientEpi f Theta) :
    IsQuotientEpi f Psi := by
  intro s q
  refine Quotient.inductionOn q ?_
  intro y
  rcases hEpi s (Quotient.mk'' y) with ⟨x, hx⟩
  refine ⟨x, Quotient.sound ?_⟩
  exact hle s _ _ (Quotient.exact hx)

private theorem pullback_syntactic_saturates {S : Type} {sig : Signature S}
    {A B : Algebra sig} (f : Hom A B) (Theta : Congruence B)
    (K : Language A) (hK : Saturated (Congruence.pullback f Theta) K) :
    Saturated
      (Congruence.pullback f
        (syntacticCongruence B (imageSaturation f Theta K))) K := by
  let N := imageSaturation f Theta K
  have hNSat : Saturated Theta N := imageSaturation_saturated f Theta K
  have hSynSat : Saturated (syntacticCongruence B N) N :=
    (syntactic_universal B N).1
  intro s x y hxy
  constructor
  · intro hx
    have hfx : f.toFun s x ∈ N s :=
      ⟨x, hx, (Theta.setoid s).refl _⟩
    have hfy : f.toFun s y ∈ N s := (hSynSat s _ _ hxy).1 hfx
    rcases hfy with ⟨z, hz, hzy⟩
    exact (hK s z y hzy).1 hz
  · intro hy
    have hfy : f.toFun s y ∈ N s :=
      ⟨y, hy, (Theta.setoid s).refl _⟩
    have hfx : f.toFun s x ∈ N s :=
      (hSynSat s _ _ ((syntacticCongruence B N).setoid s |>.symm hxy)).1 hfy
    rcases hfx with ⟨z, hz, hzx⟩
    exact (hK s z x hzx).1 hz

theorem solution {S : Type} [Finite S] {sig : Signature S}
    (L : RegularLanguageFormation sig) :
    ∃ F : FiniteIndexCongruenceFormation sig,
      ∀ X : SSet S, F.congruences X = congruencesOf L X := by
  let F : FiniteIndexCongruenceFormation sig :=
    { congruences := congruencesOf L
      nonempty := by
        intro X
        exact ⟨Congruence.top (freeAlgebra sig X),
          (finiteIndex_filter (freeAlgebra sig X)).1,
          fun K hK => L.top_saturated X hK⟩
      inter_closed := by
        intro X Phi Psi hPhi hPsi
        rcases hPhi with ⟨hPhiFin, hPhiLang⟩
        rcases hPsi with ⟨hPsiFin, hPsiLang⟩
        have hInterFin := (finiteIndex_filter (freeAlgebra sig X)).2.1
          Phi Psi hPhiFin hPsiFin
        exact ⟨hInterFin, fun K hK =>
          all_inter_saturated_selected L X Phi Psi hPhiLang hPsiLang
            hInterFin K hK⟩
      upward_closed := by
        intro X Phi Psi hPhi hle
        rcases hPhi with ⟨hPhiFin, hPhiLang⟩
        refine ⟨(finiteIndex_filter (freeAlgebra sig X)).2.2
          Phi Psi hPhiFin hle, ?_⟩
        intro K hK
        apply hPhiLang K
        intro s x y hxy
        exact hK s x y (hle s x y hxy)
      pullback_closed := by
        intro X Y Theta hTheta f hEpi
        rcases hTheta with ⟨hThetaFin, hThetaLang⟩
        refine ⟨pullback_finiteIndex f Theta hThetaFin, ?_⟩
        intro K hK
        let N := imageSaturation f Theta K
        have hNSat : Saturated Theta N := imageSaturation_saturated f Theta K
        have hN : N ∈ L.languages Y := hThetaLang N hNSat
        have hThetaSyn : Theta ≤ syntacticCongruence (freeAlgebra sig Y) N :=
          ((syntactic_universal (freeAlgebra sig Y) N).2 Theta).1 hNSat
        exact L.pullback_saturated X Y hN f
          (quotientEpi_mono f Theta
            (syntacticCongruence (freeAlgebra sig Y) N) hThetaSyn hEpi)
          (pullback_syntactic_saturates f Theta K hK)
      finite_index := by
        intro X Phi hPhi
        exact hPhi.1 }
  exact ⟨F, fun X => rfl⟩

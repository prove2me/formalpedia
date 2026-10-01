-- Prove2me | solution 1 for Grunbaum2003.closed_convex_line_free_extremePoint_exists
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:54:41.00431+00:00
-- url     : https://prove2.me/submissions/b308ef99-d3ab-4691-aeff-03872a2ee97a

import Mathlib
import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
set_option maxHeartbeats 1500000
namespace GrunbaumProof
noncomputable section
 theorem proper_supporting_face {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K:Set E) (hne:K.Nonempty) (hc:IsClosed K) (hv:Convex ℝ K)
    (hl:¬ ∃ x v:E,v ≠ 0 ∧ ∀ t:ℝ,x+t • v ∈ K) (hnsub:¬ K.Subsingleton) :
    ∃ F:Set E,F.Nonempty ∧ IsClosed F ∧ Convex ℝ F ∧ IsExtreme ℝ K F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction < Module.finrank ℝ (affineSpan ℝ K).direction := by
  obtain ⟨x,hx,y,hy,hxy⟩:=Set.not_subsingleton_iff.mp hnsub
  obtain ⟨t,ht⟩:∃ t:ℝ,x+t • (y-x) ∉ K := by
    by_contra! hh
    exact hl ⟨x,y-x,sub_ne_zero.mpr hxy.symm,hh⟩
  let u:=x+t • (y-x)
  obtain ⟨p,hp,hmin⟩:=exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv u
  have hnormal:∀ w ∈ K,inner ℝ (u-p) (w-p) ≤ 0:=
    (norm_eq_iInf_iff_real_inner_le_zero hv hp).mp hmin
  let l:E →L[ℝ] ℝ:=innerSL ℝ (u-p)
  have hbound:∀ w ∈ K,l w ≤ l p := by
    intro w hw
    have hh:=hnormal w hw
    rw [inner_sub_right] at hh
    exact sub_nonpos.mp hh
  obtain ⟨q,hq,hqstrict⟩:∃ q∈K,l q < l p := by
    by_contra! hno
    have heq:∀ w∈K,l w=l p:=fun w hw=> le_antisymm (hbound w hw) (hno w hw)
    have hlu:l u=l p := by
      dsimp [u]
      rw [map_add,map_smul,map_sub,heq x hx,heq y hy]
      simp
    have hz:l (u-p)=0 := by rw [map_sub,hlu,sub_self]
    change inner ℝ (u-p) (u-p)=0 at hz
    have hup:u=p:=sub_eq_zero.mp (inner_self_eq_zero.mp hz)
    apply ht
    change u ∈ K
    rw [hup]
    exact hp
  let A:AffineSubspace ℝ E:=AffineSubspace.mk' p (LinearMap.ker l.toLinearMap)
  have hA (w:E) : w ∈ A ↔ l w=l p := by
    simp [A,AffineSubspace.mem_mk',LinearMap.mem_ker,map_sub,sub_eq_zero]
  let F:=K ∩ (A:Set E)
  have hFn:F.Nonempty:=⟨p,hp,(hA p).mpr rfl⟩
  have hFc:IsClosed F:=hc.inter A.closed_of_finiteDimensional
  have hFv:Convex ℝ F:=hv.inter A.convex
  have hFe:IsExtreme ℝ K F := by
    refine ⟨Set.inter_subset_left,?_⟩
    rintro v hv w hw z hz ⟨a,b,ha,hb,hab,heq⟩
    refine ⟨hv,(hA v).mpr ?_⟩
    have hvle:=hbound v hv
    have hwle:=hbound w hw
    have hzeq: l z=l p:=(hA z).mp hz.2
    have hh:=congrArg l heq
    simp only [map_add,map_smul,smul_eq_mul,hzeq] at hh
    have hsum:a*l p+b*l p=l p:=by rw [←add_mul,hab,one_mul]
    have hpos:=mul_nonneg hb.le (sub_nonneg.mpr hwle)
    apply le_antisymm hvle
    nlinarith
  refine ⟨F,hFn,hFc,hFv,hFe,?_⟩
  have hle:affineSpan ℝ F ≤ affineSpan ℝ K:=affineSpan_mono ℝ Set.inter_subset_left
  have hnot:¬ affineSpan ℝ K ≤ affineSpan ℝ F := by
    intro hh
    have hFA:affineSpan ℝ F ≤ A:=affineSpan_le.mpr Set.inter_subset_right
    have hqA:q ∈ A:=hFA (hh (subset_affineSpan ℝ K hq))
    exact hqstrict.ne ((hA q).mp hqA)
  exact Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty (lt_of_le_not_ge hle hnot) (hFn.affineSpan ℝ))
 theorem linefree_extreme {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K:Set E) (hne:K.Nonempty) (hc:IsClosed K) (hv:Convex ℝ K)
    (hl:¬ ∃ x v:E,v ≠ 0 ∧ ∀ t:ℝ,x+t • v ∈ K) : (K.extremePoints ℝ).Nonempty := by
  have main:∀ n:ℕ,∀ K:Set E,K.Nonempty → IsClosed K → Convex ℝ K →
      (¬ ∃ x v:E,v ≠ 0 ∧ ∀ t:ℝ,x+t • v ∈ K) →
      Module.finrank ℝ (affineSpan ℝ K).direction=n → (K.extremePoints ℝ).Nonempty := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hne hc hv hl hdim
      by_cases hsub:K.Subsingleton
      · obtain ⟨x,hx⟩:=hne
        exact ⟨x,hx,fun _ hy _ _ _=> hsub hy hx⟩
      · obtain ⟨F,hFn,hFc,hFv,hFe,hFd⟩:=proper_supporting_face K hne hc hv hl hsub
        have hFl:¬ ∃ x v:E,v ≠ 0 ∧ ∀ t:ℝ,x+t • v ∈ F := by
          rintro ⟨x,v,hv,hh⟩
          exact hl ⟨x,v,hv,fun t=> hFe.subset (hh t)⟩
        obtain ⟨x,hx⟩:=ih _ (by omega) F hFn hFc hFv hFl rfl
        exact ⟨x,hFe.extremePoints_subset_extremePoints hx⟩
  exact main _ K hne hc hv hl rfl

 theorem fin_linefree_extreme {d:ℕ} (K:Set (Fin d → ℝ)) (hne:K.Nonempty)
    (hc:IsClosed K) (hv:Convex ℝ K)
    (hl:¬ ∃ x v:Fin d → ℝ,v ≠ 0 ∧ ∀ t:ℝ,x+t • v ∈ K) : (K.extremePoints ℝ).Nonempty := by
  let e:(Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d):=(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toContinuousLinearEquiv
  have hL:¬ ∃ x v:EuclideanSpace ℝ (Fin d),v ≠ 0 ∧ ∀ t:ℝ,x+t • v ∈ e '' K := by
    rintro ⟨x,v,hv,hh⟩
    apply hl
    refine ⟨e.symm x,e.symm v,?_,?_⟩
    · intro he
      apply hv
      have h:=congrArg e he
      simpa using h
    · intro t
      obtain ⟨y,hy,heq⟩:=hh t
      have he:=congrArg e.symm heq
      have he':y=e.symm x+t • e.symm v:=by simpa only [map_add,map_smul,e.symm_apply_apply] using he
      exact he' ▸ hy
  have hex:=linefree_extreme (e '' K) (hne.image e) (e.toHomeomorph.isClosedMap K hc) (hv.linear_image e.toLinearMap) hL
  rw [←image_extremePoints e K] at hex
  exact Set.Nonempty.of_image hex
end
end GrunbaumProof

theorem solution {d : ℕ}
    (K : Set (Fin d → ℝ)) (hne : K.Nonempty) (hline : Grunbaum2003.IsLineFree K)
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    (K.extremePoints ℝ).Nonempty := by
  exact GrunbaumProof.fin_linefree_extreme K hne hclosed hconvex hline

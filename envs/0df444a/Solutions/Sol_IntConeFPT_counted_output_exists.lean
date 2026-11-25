-- Prove2me | solution 1 for IntConeFPT.counted_output_exists
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:41:44.572894+00:00
-- url     : https://prove2.me/submissions/661632ca-eea9-4bcf-b930-cad1be2458a1

import Theorems.Thm_IntConeFPT_counted_grid
import Theorems.Thm_IntConeFPT_lemma_7

open IntConeFPT OnlineCRS.Combine
namespace IntConeFPT.CountedOutput
private lemma convex_P (I : Instance) (t : Fin I.τ) : Convex ℝ (I.P t) := by
  intro p hp q hq a b ha hb hab i
  have hpi := hp i
  have hqi := hq i
  have hsum :
      (∑ j, (I.Aloc t i j : ℝ) * (a • p + b • q).1 j) +
      (∑ j, (I.Bloc t i j : ℝ) * (a • p + b • q).2 j) =
      a * ((∑ j, (I.Aloc t i j : ℝ) * p.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p.2 j)) +
      b * ((∑ j, (I.Aloc t i j : ℝ) * q.1 j) + (∑ j, (I.Bloc t i j : ℝ) * q.2 j)) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum]
    ring
  rw [hsum]
  calc
    _ ≤ a * (I.bloc t i : ℝ) + b * (I.bloc t i : ℝ) := add_le_add (mul_le_mul_of_nonneg_left hpi ha) (mul_le_mul_of_nonneg_left hqi hb)
    _ = _ := by rw [← add_mul, hab, one_mul]

private lemma discreteJensen_X (I : Instance) (hI : I.Valid) (t : Fin I.τ) :
    DiscreteJensen {x : Fin I.d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' I.P t}
      (fun x => I.f t (fun i => (x i : ℝ))) := by
  intro x _ m θ xs hxs hθ0 hθ1 hx_eq
  have hconv := hI.convex t
  have hle := hconv.map_sum_le (fun i _ => hθ0 i) hθ1 (fun i _ => hxs i)
  rw [← hx_eq] at hle
  simpa only [smul_eq_mul] using hle

-- A rational specialization need only respect the finitely many slacks of this witness.
private lemma specialize {ι : Type} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∃ F : ℝ →ₗ[ℚ] ℚ, F 1 = 1 ∧ ∀ i, 0 ≤ F (v i) := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℝ
  let K := Module.Basis.ofVectorSpaceIndex ℚ ℝ
  let V := insert 1 ((Finset.univ.image v).filter fun r => 0 < r)
  let S : Set (K → ℝ) := ⋂ r ∈ V, {f | 0 < (b.constr ℚ f) r}
  have ho : IsOpen S := by
    apply isOpen_biInter_finset
    intro r _
    apply isOpen_lt continuous_const
    simp only [Module.Basis.constr_apply,Finsupp.sum,Rat.smul_def]
    fun_prop
  have hb : (⇑b : K → ℝ) ∈ S := by
    simp only [S,Set.mem_iInter,Set.mem_ofPred_eq]
    intro r hr
    have he : b.constr ℚ (⇑b : K → ℝ) = LinearMap.id := b.constr_self ℚ (LinearMap.id (R:=ℚ))
    change 0 < b.constr ℚ (⇑b : K → ℝ) r
    rw [he]; rcases Finset.mem_insert.mp hr with rfl | hp
    · norm_num
    · exact (Finset.mem_filter.mp hp).2
  obtain ⟨f,hf⟩ := (DenseRange.piMap (fun _ : K => Rat.denseRange_cast (𝕜:=ℝ))).exists_mem_open ho ⟨_,hb⟩
  let G := b.constr ℚ f
  have hG r (hr : r ∈ V) : 0 < G r := by
    have h := Set.mem_iInter₂.mp hf r hr
    change 0 < (b.constr ℚ (fun i => (f i : ℝ))) r at h
    have he : ((G r : ℚ) : ℝ) = _ := (show ((G r : ℚ) : ℝ) = (b.constr ℚ (fun i => (f i : ℝ))) r by
      simp [G,Module.Basis.constr_apply,Finsupp.sum,Rat.smul_def])
    exact_mod_cast (he ▸ h : (0:ℝ) < (G r : ℝ))
  have hg1 := hG 1 (Finset.mem_insert_self ..)
  refine ⟨(G 1)⁻¹ • G, by simp [hg1.ne'],fun i => ?_⟩
  by_cases h0 : v i = 0
  · simp [h0]
  · exact mul_nonneg (inv_nonneg.mpr hg1.le) (hG _ (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,lt_of_le_of_ne (hv i) (Ne.symm h0)⟩))).le

private abbrev RatGen (I : Instance) := (Fin I.d → ℤ) × (Fin I.k → ℚ)

private lemma rationalize (I : Instance) (N : ℕ) (μ : Mult I) (hf : I.FeasibleN N μ)
    (hsiz : ∀ t, (μ t).support.card ≤ 2^I.d) :
    ∃ (cert : Cert I) (y : Fin I.d → ℚ) (v : Fin I.k → ℚ),
      CertOK I cert ∧ I.FeasibleN N (certMult I cert) ∧
      I.totalAgg (certMult I cert) = ((fun j => (y j : ℝ)),fun j => (v j : ℝ)) ∧
      I.cost (certMult I cert) = I.cost μ := by
  classical
  let Local := Σ t : Fin I.τ, (μ t).support × Fin (I.m t)
  let Row := Local ⊕ (Fin I.mQ ⊕ Fin I.mA)
  let lhsL := fun t (g : Gen I.d I.k) i => (∑ j, (I.Aloc t i j : ℝ) * (g.1 j : ℝ)) +
    (∑ j, (I.Bloc t i j : ℝ) * g.2 j)
  let lhsQ := fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => fun i =>
    (∑ j, (I.QY i j : ℝ) * p.1 j) + (∑ j, (I.QV i j : ℝ) * p.2 j)
  let lhsA := fun Y : Fin I.τ → (Fin I.d → ℝ) × (Fin I.k → ℝ) × ℝ => fun i =>
    ∑ t, ((∑ j, (I.AY t i j : ℝ) * (Y t).1 j) + (∑ j, (I.AV t i j : ℝ) * (Y t).2.1 j)
       + (I.AN i t : ℝ) * (Y t).2.2)
  let slack : Row → ℝ := Sum.elim
    (fun ⟨t,g,i⟩ => (I.bloc t i : ℝ) - lhsL t g.val i)
    (Sum.elim (fun i => (I.cQ i : ℝ) - lhsQ (I.totalAgg μ) i)
      (fun i => (I.cA i : ℝ) - lhsA (I.typeAgg μ) i))
  have hn : ∀ i, 0 ≤ slack i := by
    rintro (⟨t,g,i⟩ | i | i)
    · exact sub_nonneg.mpr ((hf.1.1 t g.property) i)
    · exact sub_nonneg.mpr (hf.1.2.1 i)
    · exact sub_nonneg.mpr (hf.1.2.2 i)
  obtain ⟨F,h1,hF⟩ := specialize slack hn
  let P : ℝ →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp F
  have p1 : P 1 = 1 := by simp [P,h1]
  have pmul (a : ℚ) (x : ℝ) : P ((a:ℝ)*x) = (a:ℝ)*P x := by simpa [Rat.smul_def] using P.map_smul a x
  have prat (a : ℚ) : P (a : ℝ) = a := by simpa [p1] using pmul a 1
  have pint (a : ℤ) : P (a : ℝ) = a := by exact_mod_cast prat (a : ℚ)
  have pnat (a : ℕ) : P (a : ℝ) = a := by exact_mod_cast prat (a : ℚ)
  have pnmul (a : ℕ) (x : ℝ) : P ((a:ℝ)*x) = (a:ℝ)*P x := by simpa using pmul (a:ℚ) x
  have hP (i : Row) : 0 ≤ P (slack i) := by change (0:ℝ) ≤ (F (slack i) : ℝ); exact_mod_cast hF i
  let rg := fun g : Gen I.d I.k => (g.1,fun j => F (g.2 j))
  let realg := fun g : RatGen I => (g.1,fun j => (g.2 j : ℝ))
  let ν := fun t : Fin I.τ => (μ t).mapDomain rg
  let cert : Cert I := fun t => (ν t).support.toList.map fun g => (g.1,g.2,ν t g)
  let muR := certMult I cert
  have hMu (t) : muR t = (ν t).mapDomain realg := by
    simp only [muR,certMult,cert,List.map_map,Finset.sum_map_toList]
    rfl
  have eval {M : Type} [AddCommMonoid M] (t : Fin I.τ) (f : Gen I.d I.k → ℕ → M)
      (hzero : ∀ g, f g 0 = 0) (hadd : ∀ g a b, f g (a+b) = f g a + f g b) :
      (muR t).sum f = (μ t).sum (fun g n => f (realg (rg g)) n) := by
    rw [hMu,Finsupp.sum_mapDomain_index hzero hadd]
    exact Finsupp.sum_mapDomain_index (fun _ => hzero _) (fun _ => hadd _)
  have mem (t) (g : Gen I.d I.k) (hg : g ∈ (μ t).support) : realg (rg g) ∈ I.S t := by
    intro i
    have h := hP (.inl ⟨t,⟨g,hg⟩,i⟩)
    change 0 ≤ P ((I.bloc t i : ℝ) - lhsL t g i) at h
    change (∑ j, (I.Aloc t i j : ℝ) * (g.1 j : ℝ)) + (∑ j, (I.Bloc t i j : ℝ) * P (g.2 j)) ≤ _
    simpa only [map_sub,sub_nonneg,lhsL,prat,map_add,map_sum,pmul,pint] using h
  have hok : CertOK I cert := by
    intro t
    refine ⟨?_,?_,?_⟩
    · simp only [cert,List.length_map,Finset.length_toList]
      exact ((Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le).trans
        ((hsiz t).trans (Nat.pow_le_pow_right (by decide) (by omega)))
    · simpa [cert,List.map_map,Function.comp_def] using (ν t).support.nodup_toList
    · intro e he
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp he
      have hm := Finset.mem_toList.mp hg
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
      exact ⟨Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hm),mem t a ha⟩
  have hsup : I.Supported muR := by
    intro t g hg
    rw [hMu] at hg
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp hg))
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
    exact mem t a ha
  have hc t : count (muR t) = count (μ t) := eval t (fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)
  have hcost : I.cost muR = I.cost μ := by
    apply Finset.sum_congr rfl; intro t _
    exact eval t _ (fun _ => by simp) (fun _ _ _ => by push_cast; ring)
  have hg1 t j : (aggr (muR t)).1 j = P ((aggr (μ t)).1 j) := by
    unfold aggr
    rw [eval t (fun v n => (n:ℝ) • v.toReal) (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
    simp [aggr,Finsupp.sum,Prod.fst_sum,Gen.toReal,map_sum,pnmul,pint,realg,rg]
  have hg2 t j : (aggr (muR t)).2 j = P ((aggr (μ t)).2 j) := by
    unfold aggr
    rw [eval t (fun v n => (n:ℝ) • v.toReal) (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
    simp [Finsupp.sum,Prod.snd_sum,Gen.toReal,map_sum,pnmul,realg,rg]
    rfl
  have hy1 j : (I.totalAgg muR).1 j = P ((I.totalAgg μ).1 j) := by
    simp [Instance.totalAgg,Prod.fst_sum,map_sum,hg1]
  have hy2 j : (I.totalAgg muR).2 j = P ((I.totalAgg μ).2 j) := by
    simp [Instance.totalAgg,Prod.snd_sum,map_sum,hg2]
  refine ⟨cert,fun j => F ((I.totalAgg μ).1 j),fun j => F ((I.totalAgg μ).2 j),hok,
    ⟨⟨hsup,?_,?_⟩,?_⟩,Prod.ext (funext hy1) (funext hy2),hcost⟩
  · intro i
    have h := hP (.inr (.inl i))
    change 0 ≤ P ((I.cQ i : ℝ) - lhsQ (I.totalAgg μ) i) at h
    change lhsQ (I.totalAgg muR) i ≤ _
    simpa only [map_sub,sub_nonneg,lhsQ,prat,map_add,map_sum,pmul,hy1,hy2] using h
  · intro i
    have h := hP (.inr (.inr i))
    change 0 ≤ P ((I.cA i : ℝ) - lhsA (I.typeAgg μ) i) at h
    change lhsA (I.typeAgg muR) i ≤ _
    simpa only [map_sub,sub_nonneg,lhsA,prat,map_add,map_sum,pmul,Instance.typeAgg,hg1,hg2,hc,pnat] using h
  · simpa only [muR,Instance.totalCount] using (show I.totalCount muR ≤ N by
      simpa only [Instance.totalCount,hc] using hf.2)

end IntConeFPT.CountedOutput
open IntConeFPT.CountedOutput

theorem solution (I : Instance) (hI : I.Valid) (N : ℕ) :
    ∃ o : Output I, o.CorrectN N := by
  classical
  by_cases h : ∃ μ, I.FeasibleN N μ
  · obtain ⟨qpos,_,grid⟩ := counted_grid I hI N
    let q := ∏ t, ∏ j, (I.coeff t j).den
    let P := fun z : ℤ => ∃ μ, I.FeasibleN N μ ∧ (q:ℝ)*I.cost μ = (z:ℝ)
    have ex : ∃ z, P z := by
      obtain ⟨μ,hm⟩ := h
      obtain ⟨z,hz,_⟩ := grid μ hm
      exact ⟨z,μ,hm,hz⟩
    let L := (encInstance I ++ encNat N ++ [3]).length
    have hb : ∃ b : ℤ, ∀ z, P z → b ≤ z := by
      refine ⟨-((2^(L^2+4*L) : ℕ) : ℤ),?_⟩
      rintro z ⟨μ,hm,he⟩
      obtain ⟨z',hz,hb⟩ := grid μ hm
      have hzz : z = z' := by exact_mod_cast he.symm.trans hz
      subst z'
      exact (abs_le.mp (by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hb))).1
    obtain ⟨z,⟨μ,hμ,hz⟩,hmin⟩ := Int.exists_least_of_bdd hb ex
    have opt (ν) (hν : I.FeasibleN N ν) : I.cost μ ≤ I.cost ν := by
      obtain ⟨z',hz',_⟩ := grid ν hν
      apply le_of_mul_le_mul_left (a := (q:ℝ)) _ (Nat.cast_pos.mpr qpos)
      rw [hz,hz']; exact_mod_cast hmin z' ⟨ν,hν,hz'⟩
    obtain ⟨ν,hs,ha,hc,hsize,_⟩ := lemma_7 hI.one_le_d I.P (convex_P I) hI.bounded I.f
      (discreteJensen_X I hI) μ hμ.1.1
    have hν : I.FeasibleN N ν := by
      have hagg := fun t => (ha t).1
      have hcnt := fun t => (ha t).2
      exact ⟨⟨hs,by simpa only [Instance.totalAgg,hagg] using hμ.1.2.1,
        by simpa only [Instance.typeAgg,hagg,hcnt] using hμ.1.2.2⟩,
        by simpa only [Instance.totalCount,hcnt] using hμ.2⟩
    obtain ⟨cert,y,v,hok,hf,hagg,hcost⟩ := rationalize I N ν hν hsize
    exact ⟨.optimal y v cert,hok,hf,hagg,fun s hs => hcost.le.trans
      ((Finset.sum_le_sum fun t _ => hc t).trans (opt s hs))⟩
  · exact ⟨.infeasible,h⟩

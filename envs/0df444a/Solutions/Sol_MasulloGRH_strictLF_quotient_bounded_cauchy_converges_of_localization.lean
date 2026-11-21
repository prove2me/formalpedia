-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_bounded_cauchy_converges_of_localization
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:15:03.336462+00:00
-- url     : https://prove2.me/submissions/f8c40aa1-4fa8-4ce2-be9c-fb6aa0444385

import Definitions.Def_MasulloGRH_LocallyConvex

open MasulloGRH Set Function Filter Topology Bornology UniformSpace
open scoped Pointwise

-- The locally convex basis at the origin, using the campaign's seminorm formulation.
private theorem small_disk {G : Type*} [AddCommGroup G] [Module ℂ G] [t : TopologicalSpace G]
    (hG : IsLocallyConvexTopology G t) {U : Set G} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : G), Balanced ℂ V ∧ Convex ℝ V ∧ V ⊆ U := by
  obtain ⟨ι,_,p,hp⟩ := hG
  obtain ⟨⟨s,r⟩,hr,hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp hU
  exact ⟨(s.sup p).ball 0 r,hp.hasBasis_zero_ball.mem_of_mem (i := (s,r)) hr,
    Seminorm.balanced_ball_zero _ r,Seminorm.convex_ball _ _ _,hsub⟩

-- If the closures of an exhausting sequence of local disks bring in no new
-- points, the final locally convex topology brings in no new points either.
private theorem disk_cover_surj {Q H : Type*} [AddCommGroup Q] [Module ℂ Q] [t : TopologicalSpace Q]
    [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    (hQ : ∀ U ∈ 𝓝 (0 : Q), ∃ V ∈ 𝓝 (0 : Q), Balanced ℂ V ∧ Convex ℝ V ∧ V ⊆ U) (j : Q →+ H) (hj : IsDenseInducing j)
    (N : ℕ → Filter Q) (hN : ∀ n, N n ≤ 𝓝 0)
    (hfinal : ∀ W : Set Q, Balanced ℂ W → Convex ℝ W → (∀ n, W ∈ N n) → W ∈ 𝓝 0)
    (D : ℕ → Set Q) (hD : ∀ n, D n ∈ N n) (h0 : ∀ n, (0 : Q) ∈ D n)
    (hbal : ∀ n, Balanced ℂ (D n)) (hconv : ∀ n, Convex ℝ (D n))
    (hmono : Monotone D) (hcover : ∀ x, ∃ n, x ∈ D n)
    (hclosed : ∀ n, closure (j '' (D n + D n)) ⊆ range j) : Surjective j := by
  intro y
  by_contra hy
  have hsep (n : ℕ) : ∃ O ∈ 𝓝 y, ∃ V ∈ 𝓝 (0 : Q), Balanced ℂ V ∧ Convex ℝ V ∧
      ∀ u ∈ O, ∀ v ∈ V, u - j v ∉ j '' (D n + D n) := by
    let A := j '' (D n + D n)
    have hA : (closure A)ᶜ ∈ 𝓝 y :=
      isClosed_closure.isOpen_compl.mem_nhds (fun h => hy (hclosed n h))
    have hcont : Continuous (fun z : H × Q => z.1 - j z.2) := continuous_fst.sub (hj.continuous.comp continuous_snd)
    have hprod := hcont.continuousAt.preimage_mem_nhds (x := (y,(0 : Q))) (by simpa using hA)
    rw [nhds_prod_eq] at hprod
    obtain ⟨O,hO,P,hP,hOP⟩ := mem_prod_iff.mp hprod
    obtain ⟨V,hV,hVb,hVc,hVP⟩ := hQ _ hP
    exact ⟨O,hO,V,hV,hVb,hVc,fun u hu v hv hmem => hOP (show (u,v) ∈ O ×ˢ P from ⟨hu,hVP hv⟩) (subset_closure hmem)⟩
  choose O hO V hV hVb hVc hsep using hsep
  let W := ⋂ n, (D n + V n)
  have hW : W ∈ 𝓝 (0 : Q) := by
    apply hfinal _ (balanced_iInter fun n => (hbal n).add (hVb n)) (convex_iInter fun n => (hconv n).add (hVc n))
    intro k
    have hsmall := inter_mem (hD k) ((biInter_finset_mem (Finset.range k)).mpr (fun n _ => hN k (hV n)))
    apply mem_of_superset hsmall
    rintro x ⟨hx,hv⟩
    apply mem_iInter.mpr
    intro n
    by_cases h : k ≤ n
    · exact ⟨x,hmono h hx,0,mem_of_mem_nhds (hV n),add_zero _⟩
    · exact ⟨0,h0 n,x,mem_iInter₂.mp hv n (Finset.mem_range.mpr (lt_of_not_ge h)),zero_add _⟩
  have hjW : closure (j '' W) ∈ 𝓝 (0 : H) := by simpa using hj.closure_image_mem_nhds hW
  have hyW : {z : H | y-z ∈ closure (j '' W)} ∈ 𝓝 y := by
    apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
    simpa using hjW
  obtain ⟨_,hx,⟨x,rfl⟩⟩ := mem_closure_iff_nhds.mp (hj.dense y) _ hyW
  change y - j x ∈ closure (j '' W) at hx
  obtain ⟨n,hn⟩ := hcover x
  have hlim : y ∈ closure ((fun w : H => j x + w) '' (j '' W)) := by
    have h := image_closure_subset_closure_image (show Continuous (fun w : H => j x + w) from continuous_const.add continuous_id) (mem_image_of_mem _ hx)
    simpa using h
  obtain ⟨z,hz,_,hw,rfl⟩ := (mem_closure_iff_nhds.mp hlim) _ (hO n)
  obtain ⟨w,hw,rfl⟩ := hw
  obtain ⟨d,hd,v,hv,rfl⟩ := mem_iInter.mp hw n
  apply hsep n _ hz v hv
  refine ⟨x+d,add_mem_add hn hd,?_⟩
  simp [map_add, ← add_assoc]

private def stableAt {Q : Type*} [Zero Q] [TopologicalSpace Q] (A : Set Q) (F : Filter Q) : Prop :=
  ∀ W ∈ F, ∃ G ∈ 𝓝 (0 : Q), A ∩ G ⊆ W

private structure StageDisk {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (N : ℕ → Filter Q) (Y : ℕ → Submodule ℝ Q) (n : ℕ) where
  carrier : Set Q
  step : ℕ
  le_step : n ≤ step
  nhd : carrier ∈ N n
  zero : 0 ∈ carrier
  bal : Balanced ℂ carrier
  conv : Convex ℝ carrier
  sub : carrier ⊆ (Y step : Set Q)
  stable : stableAt carrier (N step)

private theorem stable_scale {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    [ContinuousConstSMul ℝ Q] {A : Set Q} {F : Filter Q} (hF : ∀ c : ℝ, Tendsto (c • ·) F F)
    (hA : stableAt A F) {c : ℝ} (hc : c ≠ 0) : stableAt (c • A) F := by
  intro W hW
  obtain ⟨G,hG,hsub⟩ := hA _ (hF c hW)
  refine ⟨c • G, (set_smul_mem_nhds_zero_iff hc).mpr hG, ?_⟩
  rintro x ⟨⟨a,ha,rfl⟩,hx⟩
  exact hsub ⟨ha,by simpa [mem_smul_set_iff_inv_smul_mem₀ hc, inv_smul_smul₀ hc] using hx⟩

private theorem stageDisk_next {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [t : TopologicalSpace Q]
    [IsTopologicalAddGroup Q] [ContinuousConstSMul ℝ Q]
    (hQ : ∀ U ∈ 𝓝 (0 : Q), ∃ V ∈ 𝓝 (0 : Q), Balanced ℂ V ∧ Convex ℝ V ∧ V ⊆ U) {N : ℕ → Filter Q} {Y : ℕ → Submodule ℝ Q}
    (hN : ∀ i, N i ≤ 𝓝 0) (hNmono : Monotone N) (hYmono : Monotone Y)
    (hscale : ∀ n (c : ℝ), Tendsto (c • ·) (N n) (N n))
    (base : ∀ n, Nonempty (StageDisk N Y n)) {n : ℕ} (A : StageDisk N Y n) :
    ∃ B : StageDisk N Y (n+1), (2:ℝ) • A.carrier ⊆ B.carrier := by
  let k := max A.step (n+1)
  let B := Classical.choice (base k)
  let C := (1/2:ℝ) • B.carrier
  have hC : C ∈ N k := by
    apply mem_of_superset (show (fun x : Q => (2:ℝ) • x) ⁻¹' B.carrier ∈ N k from hscale k 2 B.nhd)
    intro x hx
    exact ⟨(2:ℝ) • x,hx,by dsimp; rw [smul_smul]; norm_num⟩
  obtain ⟨G,hG,hAC⟩ := stable_scale (hscale A.step) A.stable (c := 2) (by norm_num)
    C (hNmono (le_max_left _ _) hC)
  obtain ⟨P,hP,hPP⟩ := exists_nhds_zero_half hG
  obtain ⟨V,hV,hVb,hVc,hVP⟩ := hQ _ hP
  have hneg {v : Q} (hv : v ∈ V) : -v ∈ V := by
    rw [← hVb.neg_eq]
    exact neg_mem_neg.mpr hv
  let S := (2:ℝ) • A.carrier + (C ∩ V)
  have h0A : (0:Q) ∈ (2:ℝ) • A.carrier := ⟨0,A.zero,smul_zero _⟩
  have h0C : (0:Q) ∈ C := ⟨0,B.zero,smul_zero _⟩
  have h0V := mem_of_mem_nhds hV
  have hsub : S ∩ V ⊆ B.carrier := by
    rintro _ ⟨⟨a,ha,b,⟨hb,hbv⟩,rfl⟩,hv⟩
    have haG : a ∈ G := by
      simpa using hPP _ (hVP hv) _ (hVP (hneg hbv))
    obtain ⟨x,hx,rfl⟩ := hAC ⟨ha,haG⟩
    obtain ⟨y,hy,rfl⟩ := hb
    have hmid := B.conv.midpoint_mem hx hy
    simpa [midpoint_eq_smul_add, invOf_eq_inv, smul_add, one_div] using hmid
  refine ⟨{carrier := S, step := B.step, le_step := (le_max_right _ _).trans B.le_step
           nhd := ?_, zero := ?_, bal := ?_, conv := ?_, sub := ?_, stable := ?_},?_⟩
  · apply mem_of_superset (hNmono (le_max_right _ _) (inter_mem hC (hN k hV)))
    exact fun x hx => ⟨0,h0A,x,hx,zero_add _⟩
  · exact ⟨0,h0A,0,⟨h0C,h0V⟩,zero_add _⟩
  · exact (Balanced.smul (2:ℝ) A.bal).add ((Balanced.smul (1/2:ℝ) B.bal).inter hVb)
  · exact (A.conv.smul 2).add ((B.conv.smul (1/2)).inter hVc)
  · rintro _ ⟨_,⟨a,ha,rfl⟩,_,⟨⟨b,hb,rfl⟩,_⟩,rfl⟩
    exact (Y B.step).add_mem ((Y B.step).smul_mem _ (hYmono ((le_max_left _ _).trans B.le_step) (A.sub ha)))
      ((Y B.step).smul_mem _ (B.sub hb))
  · intro W hW
    obtain ⟨J,hJ,hBJ⟩ := B.stable W hW
    exact ⟨V ∩ J,inter_mem hV hJ,fun x hx => hBJ ⟨hsub ⟨hx.1,hx.2.1⟩,hx.2.2⟩⟩
  · exact fun x hx => ⟨x,hx,0,⟨h0C,h0V⟩,add_zero _⟩

private theorem make_disks {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    {N : ℕ → Filter Q} {Y : ℕ → Submodule ℝ Q} (base : Nonempty (StageDisk N Y 0))
    (next : ∀ {n} (D : StageDisk N Y n), ∃ D' : StageDisk N Y (n+1), (2:ℝ) • D.carrier ⊆ D'.carrier)
    (habs : ∀ x : Q, ∃ n, ∀ U ∈ N n, ∃ k : ℕ, ((1/2 : ℝ)^k) • x ∈ U) :
    ∃ D : ∀ n, StageDisk N Y n, Monotone (fun n => (D n).carrier) ∧ ∀ x, ∃ n, x ∈ (D n).carrier := by
  classical
  let D : ∀ n, StageDisk N Y n := Nat.rec (Classical.choice base) (fun _ a => (next a).choose)
  have hd (n : ℕ) : (2:ℝ) • (D n).carrier ⊆ (D (n+1)).carrier := (next (D n)).choose_spec
  have hx2 {x : Q} {n : ℕ} (hx : x ∈ (D n).carrier) : (2:ℝ) • x ∈ (D (n+1)).carrier :=
    hd n (smul_mem_smul_set hx)
  refine ⟨D, monotone_nat_of_le_succ (fun n x hx => ?_), ?_⟩
  · have hs := (balanced_iff_smul_mem.mp (D n).bal) (a := (1/2 : ℂ)) (by norm_num)
      (x := x) hx
    have hs' : (1/2 : ℝ) • x ∈ (D n).carrier := by simpa [← Complex.coe_smul] using hs
    simpa [smul_smul] using hx2 hs'
  · intro x
    obtain ⟨n,hn⟩ := habs x
    obtain ⟨k,hk⟩ := hn (D n).carrier (D n).nhd
    refine ⟨n+k,?_⟩
    clear hn
    induction k generalizing n with
    | zero => simpa using hk
    | succ l ih =>
      have h := hx2 hk
      have hs : ((1/2:ℝ)^l) • x ∈ (D (n+1)).carrier := by
        simpa [pow_succ,smul_smul,mul_left_comm,mul_comm,mul_assoc] using h
      have hh := ih (n+1) hs
      change x ∈ (D (n + (l+1))).carrier
      rw [show n + (l+1) = n+1+l by omega]
      exact hh

private theorem closed_stage_disk {P Q H : Type*}
    [AddCommGroup P] [Module ℂ P] [TopologicalSpace P]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [ContinuousConstSMul ℝ Q]
    [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H]
    (i : P →+ Q) (hi : Injective i) (hiC : Continuous i) (hP : IsCompleteTVS P)
    (j : Q →+ H) (hj : IsInducing j) {A : Set Q} (hsub : A ⊆ range i)
    (hconv : Convex ℝ A) (hbal : Balanced ℂ A)
    (hst : stableAt ((4:ℝ) • A) (map i (𝓝 0))) : closure (j '' (A + A)) ⊆ range j := by
  let B := A + A
  have hBrange : B ⊆ range i := by
    rintro _ ⟨_,hp,_,hq,rfl⟩
    obtain ⟨p,rfl⟩ := hsub hp
    obtain ⟨q,rfl⟩ := hsub hq
    exact ⟨p+q,map_add ..⟩
  have hdouble {x y : Q} (hx : x ∈ A) (hy : y ∈ A) : x+y ∈ (2:ℝ) • A := by
    exact ⟨midpoint ℝ x y,hconv.midpoint_mem hx hy,by simp [two_smul, midpoint_add_self]⟩
  have hdiff {x y : Q} (hx : x ∈ B) (hy : y ∈ B) : x-y ∈ (4:ℝ) • A := by
    obtain ⟨a,ha,b,hb,rfl⟩ := hx
    obtain ⟨c,hc,d,hd,rfl⟩ := hy
    obtain ⟨u,hu,hu'⟩ := hdouble ha hb
    obtain ⟨v,hv,hv'⟩ := hdouble hc hd
    have hnv : -v ∈ A := by rw [← hbal.neg_eq]; exact neg_mem_neg.mpr hv
    obtain ⟨w,hw,hw'⟩ := hdouble hu hnv
    refine ⟨w,hw,?_⟩
    change (4:ℝ) • w = a + b - (c + d)
    rw [←hu',←hv', ← smul_sub,sub_eq_add_neg,←hw',smul_smul]
    norm_num
  let T := {p : P // i p ∈ B}
  let g : T → H := fun p => j (i p.val)
  intro y hy
  have hy' : y ∈ closure (range g) := by
    apply closure_mono _ hy
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨p,rfl⟩ := hBrange hx
    exact ⟨⟨p,hx⟩,rfl⟩
  let f := comap g (𝓝 y)
  have hf : NeBot f := comap_neBot_iff.mpr fun U hU => by
    obtain ⟨_,hz,⟨z,rfl⟩⟩ := mem_closure_iff_nhds.mp hy' U hU
    exact ⟨z,hz⟩
  have hfg : Tendsto g f (𝓝 y) := tendsto_comap
  have hcf : IsCauchyFilter (map (Subtype.val : T → P) f) := by
    refine ⟨inferInstance,fun U hU => ?_⟩
    obtain ⟨V,hV,hVU⟩ := hst (i '' U) (image_mem_map hU)
    rw [hj.nhds_eq_comap, map_zero] at hV
    obtain ⟨V',hV',hVsub⟩ := mem_comap.mp hV
    have hs : Continuous (fun z : H × H => z.1-z.2) := continuous_fst.sub continuous_snd
    obtain ⟨O,hO,O',hO',hOO⟩ := mem_nhds_prod_iff.mp
      (hs.continuousAt.preimage_mem_nhds (x := (y,y)) (by simpa using hV'))
    let K := g ⁻¹' (O ∩ O')
    refine ⟨Subtype.val '' K, image_mem_map (show K ∈ f from hfg (inter_mem hO hO')),?_⟩
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    have hv : i a.val - i b.val ∈ V := hVsub (by
      change j (i a.val - i b.val) ∈ V'
      rw [map_sub]
      exact hOO (show (g a,g b) ∈ O ×ˢ O' from ⟨ha.1,hb.2⟩))
    obtain ⟨d,hd,he⟩ := hVU ⟨hdiff a.property b.property,hv⟩
    exact hi (he.trans (map_sub i a.val b.val).symm) ▸ hd
  obtain ⟨p,hp⟩ := hP.2 _ hcf
  have hlim : Tendsto g f (𝓝 (j (i p))) :=
    ((hj.continuous.comp hiC).continuousAt.tendsto).comp (show Tendsto _ f (𝓝 p) from hp)
  exact ⟨i p,tendsto_nhds_unique hlim hfg⟩

universe u

private theorem final_lf_disk {E : Type u} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    (X : ℕ → Submodule ℂ E) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hX : ∀ n, IsFrechet (X n))
    (htop : tE = sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (D : Set E) (hDbal : Balanced ℂ D) (hDconv : Convex ℝ D)
    (hW : ∀ n, (Subtype.val : X n → E) ⁻¹' D ∈ 𝓝 0) : D ∈ 𝓝 (0 : E) := by
  have hDabs : Absorbent ℝ D := by
    rw [absorbent_iff_eventually_nhdsNE_zero]
    intro x
    obtain ⟨n,hn⟩ := hexh x
    obtain ⟨ι,_,p,hp⟩ := (hX n).1
    let : ContinuousSMul ℂ (X n) := hp.continuousSMul
    let z : X n := ⟨x,hn⟩
    have hc : Continuous (fun r : ℝ => (r : ℂ) • z) := Complex.continuous_ofReal.smul continuous_const
    have hz : Tendsto (fun r : ℝ => (r : ℂ) • z) (𝓝 0) (𝓝 0) := by
      simpa using hc.continuousAt (x := (0 : ℝ)) |>.tendsto
    exact (hz.mono_left nhdsWithin_le_nhds).eventually (hW n)
  let p := gaugeSeminorm hDbal hDconv hDabs
  have hp : Continuous p := by
    let family : SeminormFamily ℂ E (ULift.{u} (Fin 1)) := fun _ => p
    let τ : ∀ n, TopologicalSpace (X n) := fun _ => inferInstance
    let t := family.moduleFilterBasis.topology
    have ht : @WithSeminorms ℂ E (ULift.{u} (Fin 1)) _ _ _ family t := ⟨rfl⟩
    have hinc (n : ℕ) : @Continuous (X n) E (τ n) t Subtype.val := by
      let : TopologicalSpace (X n) := τ n
      obtain ⟨ι,_,pn,hpn⟩ := (hX n).1
      let : ContinuousSMul ℂ (X n) := hpn.continuousSMul
      let : IsTopologicalAddGroup (X n) := hpn.topologicalAddGroup
      apply ht.continuous_of_continuous_comp (X n).subtype
      intro i
      exact Seminorm.continuous' (r := 1) (mem_of_superset (hW n) fun x hx =>
        by rw [Seminorm.closedBall_zero_eq]; exact gauge_le_one_of_mem hx)
    have hle : tE ≤ t := htop.trans_le (sInf_le ⟨⟨ULift.{u} (Fin 1),inferInstance,family,ht⟩,hinc⟩)
    exact continuous_iff_le_induced.mpr (hle.trans (continuous_iff_le_induced.mp (ht.continuous_seminorm ⟨0⟩)))
  have hb : p.ball 0 1 ∈ 𝓝 (0 : E) := by
    rw [p.ball_zero_eq]
    exact (hp.continuousAt (x := 0)).preimage_mem_nhds (t := Iio 1) (by simpa using Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
  exact mem_of_superset hb fun x hx => setOfPred_gauge_lt_one_subset_self hDconv hDabs.zero_mem hDabs
    (by rwa [p.ball_zero_eq] at hx)

private theorem balanced_image_linear {P Q : Type*} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] (f : P →ₗ[ℂ] Q) {A : Set P} (hA : Balanced ℂ A) :
    Balanced ℂ (f '' A) := by
  rw [balanced_iff_smul_mem]
  rintro c hc _ ⟨x,hx,rfl⟩
  exact ⟨c • x,balanced_iff_smul_mem.mp hA hc hx,map_smul f c x⟩

theorem solution (E : Type*) [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hL : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ W ∈ nhds (0 : X m),
      ∃ G ∈ nhds (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x : E) - (w : E)) ∈ V)
    (hP : ∀ m : ℕ, IsCompleteTVS (X m ⧸ V.comap (X m).subtype)) :
    ∀ f : Filter (E ⧸ V), IsCauchyFilter f → (∃ B ∈ f, Bornology.IsVonNBounded ℂ B) →
      ∃ x : E ⧸ V, f ≤ nhds x := by
  classical
  have hF (n : ℕ) := (hX n).1
  have hpoly : PolynormableSpace ℂ E := by
    rw [htop]
    apply PolynormableSpace.sInf
    rintro t ⟨⟨ι,_,p,hp⟩,_⟩
    exact hp.toPolynormableSpace
  have hp := PolynormableSpace.withSeminorms ℂ E
  have hE : IsLocallyConvexTopology E ‹TopologicalSpace E› := ⟨_,⟨⟨0,continuous_zero⟩⟩,_,hp⟩
  let : IsTopologicalAddGroup E := hp.topologicalAddGroup
  let : ContinuousSMul ℂ E := hp.continuousSMul
  let : IsClosed (V.toAddSubgroup : Set E) := hV
  let Q := E ⧸ V
  let : T2Space Q := QuotientAddGroup.instT2Space
  let : ContinuousConstSMul ℝ Q := ⟨fun r => (show Continuous (fun z : Q => (r:ℂ) • z) from continuous_const_smul _)⟩
  let b (n : ℕ) : X n →ₗ[ℂ] Q := V.mkQ.comp (X n).subtype
  let N (n : ℕ) : Filter Q := map (b n) (𝓝 0)
  let Y (n : ℕ) : Submodule ℝ Q := (LinearMap.range (b n)).restrictScalars ℝ
  have hb (n : ℕ) : Continuous (b n) := V.isOpenQuotientMap_mkQ.continuous.comp continuous_subtype_val
  have hN (n : ℕ) : N n ≤ 𝓝 0 := by
    change Tendsto (b n) (𝓝 0) (𝓝 0)
    simpa using (hb n).continuousAt (x := 0) |>.tendsto
  have hNmono : Monotone N := by
    intro n m hnm U hU
    let a := Submodule.inclusion (hmono hnm)
    have hc : Continuous a := continuous_subtype_val.subtype_mk _
    exact (show Tendsto a (𝓝 0) (𝓝 0) by simpa using hc.continuousAt (x := 0) |>.tendsto) (show (b m) ⁻¹' U ∈ 𝓝 0 from hU)
  have hYmono : Monotone Y := by
    rintro n m hnm _ ⟨x,rfl⟩
    exact ⟨Submodule.inclusion (hmono hnm) x,rfl⟩
  have hscale (n : ℕ) (c : ℝ) : Tendsto (c • ·) (N n) (N n) := by
    intro W hW
    have hc : Continuous (fun x : X n => (c:ℂ) • x) := continuous_const_smul _
    have hz : Tendsto (fun x : X n => (c:ℂ) • x) (𝓝 0) (𝓝 0) := by simpa using hc.continuousAt (x := 0) |>.tendsto
    exact mem_of_superset (show (fun x : X n => (c:ℂ) • x) ⁻¹' (b n ⁻¹' W) ∈ 𝓝 0 from hz hW)
      fun x hx => by simpa [mem_preimage,map_smul] using hx
  have hQbasis : ∀ U ∈ 𝓝 (0 : Q), ∃ A ∈ 𝓝 (0 : Q), Balanced ℂ A ∧ Convex ℝ A ∧ A ⊆ U := by
    intro U hU
    obtain ⟨D,hD,hDb,hDc,hDU⟩ := small_disk hE
      (show V.mkQ ⁻¹' U ∈ 𝓝 0 from V.isOpenQuotientMap_mkQ.continuous.continuousAt.preimage_mem_nhds (by simpa using hU))
    refine ⟨V.mkQ '' D,?_,balanced_image_linear _ hDb,hDc.linear_image (V.mkQ.restrictScalars ℝ),image_subset_iff.mpr hDU⟩
    simpa using V.isOpenQuotientMap_mkQ.isOpenMap.image_mem_nhds hD
  have hfinal (W : Set Q) (hWb : Balanced ℂ W) (hWc : Convex ℝ W) (hW : ∀ n, W ∈ N n) : W ∈ 𝓝 0 := by
    have hpre : V.mkQ ⁻¹' W ∈ 𝓝 0 := by
      apply final_lf_disk X hexh hF htop _ _ (hWc.linear_preimage (V.mkQ.restrictScalars ℝ)) hW
      rw [balanced_iff_smul_mem]
      exact fun c hc x hx => by simpa [mem_preimage] using balanced_iff_smul_mem.mp hWb hc hx
    have hw : W ∈ map V.mkQ (𝓝 0) := hpre
    rwa [V.isOpenQuotientMap_mkQ.map_nhds_eq,map_zero] at hw
  have base (n : ℕ) : Nonempty (StageDisk N Y n) := by
    obtain ⟨m,hnm,U,hU,hloc⟩ := hL n
    obtain ⟨D,hD,hDb,hDc,hDU⟩ := small_disk (hF n).1 hU
    refine ⟨{carrier := b n '' D, step := m, le_step := hnm, nhd := image_mem_map hD
             zero := ⟨0,mem_of_mem_nhds hD,map_zero _⟩, bal := balanced_image_linear _ hDb,
             conv := hDc.linear_image ((b n).restrictScalars ℝ), sub := ?_, stable := ?_}⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨Submodule.inclusion (hmono hnm) x,rfl⟩
    · intro W hW
      obtain ⟨G,hG,hGW⟩ := hloc ((b m) ⁻¹' W) hW
      refine ⟨G,hG,?_⟩
      rintro _ ⟨⟨x,hx,rfl⟩,hg⟩
      obtain ⟨w,hw,he⟩ := hGW x (hDU hx) hg
      have heq : b n x = b m w := (Submodule.Quotient.eq V).mpr he
      exact heq ▸ hw
  have habs (x : Q) : ∃ n, ∀ U ∈ N n, ∃ k : ℕ, ((1/2:ℝ)^k) • x ∈ U := by
    obtain ⟨y,rfl⟩ := V.mkQ_surjective x
    obtain ⟨n,hn⟩ := hexh y
    refine ⟨n,fun U hU => ?_⟩
    let z : X n := ⟨y,hn⟩
    have hpow : Tendsto (fun k : ℕ => (1/2:ℝ)^k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hc : Continuous (fun r : ℝ => (r:ℂ) • z) := Complex.continuous_ofReal.smul continuous_const
    have hz : Tendsto (fun k : ℕ => (((1/2:ℝ)^k : ℝ):ℂ) • z) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Complex.ofReal_zero,zero_smul] using (hc.continuousAt (x := 0)).tendsto.comp hpow
    obtain ⟨k,hk⟩ := (hz.eventually (show b n ⁻¹' U ∈ 𝓝 0 from hU)).exists
    refine ⟨k,?_⟩
    change b n ((((1/2:ℝ)^k : ℝ):ℂ) • z) ∈ U at hk
    rw [map_smul] at hk
    exact hk
  obtain ⟨D,hDmono,hDcover⟩ := make_disks (base 0) (stageDisk_next hQbasis hN hNmono hYmono hscale base) habs
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  let : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  let j : Q →+ Completion Q := Completion.toCompl
  have hj : IsDenseInducing j := Completion.isDenseInducing_coe
  have hclosed (n : ℕ) : closure (j '' ((D n).carrier + (D n).carrier)) ⊆ range j := by
    let m := (D n).step
    let K := LinearMap.ker (b m)
    let i := K.liftQ (b m) (le_refl K)
    have hi : Injective i := LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot' (b m) rfl)
    have hiC : Continuous i := K.isOpenQuotientMap_mkQ.continuous_comp_iff.mp (hb m)
    have hK : K = V.comap (X m).subtype := by
      ext x
      exact Submodule.Quotient.mk_eq_zero V
    have hcomplete : IsCompleteTVS (X m ⧸ K) := hK ▸ hP m
    have hNmap : N m = map i (𝓝 0) := by
      rw [← K.mkQ.map_zero,← K.isOpenQuotientMap_mkQ.map_nhds_eq,Filter.map_map]
      rfl
    apply closed_stage_disk i.toAddMonoidHom hi hiC hcomplete j hj.isInducing ?_ (D n).conv (D n).bal ?_
    · intro x hx
      obtain ⟨z,rfl⟩ := (D n).sub hx
      exact ⟨K.mkQ z,rfl⟩
    · change stableAt ((4:ℝ) • (D n).carrier) (map i (𝓝 0))
      rw [←hNmap]
      exact stable_scale (hscale m) (D n).stable (by norm_num)
  have hsur := disk_cover_surj hQbasis j hj N hN hfinal _ (fun n => (D n).nhd)
    (fun n => (D n).zero) (fun n => (D n).bal) (fun n => (D n).conv) hDmono hDcover hclosed
  intro f hf _
  have hcau : Cauchy f := by
    refine ⟨hf.1, fun T hT => ?_⟩
    rw [uniformity_eq_comap_nhds_zero] at hT
    obtain ⟨U,hU,hUT⟩ := mem_comap.mp hT
    obtain ⟨A,hA,hAA⟩ := hf.2 U hU
    exact mem_of_superset (prod_mem_prod hA hA) (fun z hz => hUT (hAA z.2 hz.2 z.1 hz.1))
  obtain ⟨y,hy⟩ := CompleteSpace.complete (hcau.map (Completion.uniformContinuous_coe Q))
  obtain ⟨x,rfl⟩ := hsur y
  exact ⟨x,(hj.isInducing.tendsto_nhds_iff).mpr (show Tendsto j f (𝓝 (j x)) from hy)⟩

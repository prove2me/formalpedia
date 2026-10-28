-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:27:19.273269+00:00
-- url     : https://prove2.me/submissions/3aa196e1-2c1d-431f-8c7a-6c845e453837

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_forward_prepared_stage
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_high_prepared_impossible
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_high_three_prepared_impossible

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_DomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

attribute [local instance] OAI.SharpRamseyFive.Marking.dtPDE
attribute [local instance] OAI.SharpRamseyFive.Marking.dtDDE
attribute [local instance] OAI.SharpRamseyFive.Marking.dtDDDE
omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma swapDomain_first_card (D : Finset (FlagPair K V)) :
    ((swapDomain D).image Prod.fst).card=(D.image Prod.snd).card := by
  congr 1
  ext b
  simp only [swapDomain,Finset.mem_image,Finset.mem_map]
  aesop

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma swapDomain_second_card (D : Finset (FlagPair K V)) :
    ((swapDomain D).image Prod.snd).card=(D.image Prod.fst).card := by
  have he : (swapDomain D).image Prod.snd=(D.image Prod.fst).map bidualPoint.toEmbedding := by
    ext b
    simp only [swapDomain,Finset.mem_image,Finset.mem_map]
    aesop
  rw [he,Finset.card_map]

omit [Fintype (ℙ K (Dual K V))] in
lemma swapDomain_first_partners (D : Finset (FlagPair K V)) (b : ℙ K (Dual K V)) :
    (Finset.univ.filter fun c=>(b,c)∈swapDomain D).card=
      (Finset.univ.filter fun a=>(a,b)∈D).card := by
  apply Eq.symm
  apply Finset.card_equiv bidualPoint
  intro a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (mem_swapDomain_iff D (a,b)).symm

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma swapDomain_second_partners (D : Finset (FlagPair K V)) (c : ℙ K (Dual K (Dual K V))) :
    (Finset.univ.filter fun b=>(b,c)∈swapDomain D).card=
      (Finset.univ.filter fun b=>(bidualPoint.symm c,b)∈D).card := by
  congr 1
  ext b
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hh:=mem_swapDomain_iff D (bidualPoint.symm c,b)
  simpa only [swapFlag_apply,Equiv.apply_symm_apply] using hh

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma ReverseCaps.swap {D : Finset (FlagPair K V)} {u : ℝ} (h : ReverseCaps D u) :
    ForwardCaps (swapDomain D) u := by
  simpa only [ForwardCaps,ReverseCaps,swapDomain_first_card,swapDomain_second_card] using h

lemma HighCaps.swap {D : Finset (FlagPair K V)} {r r' : ℕ} (h : HighCaps D r r') :
    HighCaps (swapDomain D) r' r := by
  constructor
  · simpa only [swapDomain,Finset.card_map] using h.flag
  · simpa only [swapDomain_first_card] using h.second
  · simpa only [swapDomain_second_card] using h.first
  · intro b
    simpa only [swapDomain_first_partners] using h.secondPartners b
  · intro c
    simpa only [swapDomain_second_partners] using h.firstPartners (bidualPoint.symm c)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_HighThreePrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_no_high_class {η : ℝ} (hη : 0<η) (c C Cb Cm : ℝ)
    (hc : 0 < c) (hCb : 0≤Cb) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
      [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) [Nonempty (Fin n)] (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
      (ctx : Ω→κ) (D J B M width : ℝ) (P : Prepared S ctx J B M) (r s : Fin 5),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      σ^beta η≤D→D≤σ^(1-η/2)→B≤Cb*n*D*σ^(-beta η)→M≤Cm*σ→4*σ≤J→
      (∀a,0 < map S.law ctx a→∀i,DomainClass width (P.domain a i) (.inr (.inr (r,s))))→False := by
  filter_upwards [eventually_high_prepared_impossible hη c C Cb hc hCb,
    eventually_high_three_prepared_impossible hη c Cb Cm hc hCb hCm] with σ hfour hthree
  intro K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n _ adm S ctx D J B M width P r s
    hd hσ hq hα hN hlen hC hD hDhi hB hM hJ hcl
  have hcap : ∀a,0 < map S.law ctx a→∀i,HighCaps (P.domain a i) r.val s.val :=
    fun a ha i=>(hcl a ha i).2
  obtain ⟨a,hap⟩:=(map S.law ctx).exists_positive
  have hn : 0<n := by have:=Fintype.card_pos (α:=Fin n);simpa using this
  have hsum:= (hcl a hap ⟨0,by omega⟩).1
  by_cases hr : r.val=4
  · apply hfour K V Ω κ α N n s.val adm S ctx D J B M P hd hσ hq hα hN hlen hC hD hDhi hB hJ
      (by omega) (by omega)
    simpa only [hr] using hcap
  · by_cases hs : s.val=4
    · let : Fintype (ℙ K (Dual K (Dual K (Dual K V)))) :=
        Fintype.ofEquiv (ℙ K (Dual K V)) bidualPoint
      let : Nonempty (ℙ K (Dual K (Dual K (Dual K V)))) :=
        ⟨bidualPoint (Classical.arbitrary (ℙ K (Dual K V)))⟩
      apply hfour K (Dual K V) Ω κ α N n r.val adm
        (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply)
        ctx D J B M P.swap (by simpa using hd) hσ hq hα hN hlen hC hD hDhi hB hJ
        (by omega) (by omega)
      intro a ha i
      have hh:=(hcap a ha i.rev).swap
      simpa only [Prepared.swap,hs] using hh
    · have hr3 : r.val=3 := by omega
      have hs3 : s.val=3 := by omega
      apply hthree K V Ω κ α N n adm S ctx D J B M P hd hσ hq hlen hD hDhi hB hM hJ
      simpa only [hr3,hs3] using hcap
end

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_PreparedDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section

theorem eventually_prepared_dispatch_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c C Cm C₀ : ℝ) (hc : 0 < c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
      [Fintype Ω] [Fintype κ] [Fintype α] [Nonempty α],
    ∀ (N m l : ℕ) (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N m admissible)
      (ctx : Ω→κ) (D B M k₀ : ℝ)
      (PS : Prepared S ctx (Real.log (153*(Nat.card K:ℝ)^4)) B M) (a : SlotClass),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→S.density≤C₀→8≤ m→
      σ^beta η≤D→D≤σ^(1-η/2)→c*(Nat.card K:ℝ)*σ^(1+η)≤ m→
      (m:ℝ)≤(Nat.card K:ℝ)*σ^(1+η)→(l:ℝ)≤ m/100→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤B→B≤C*m*D*σ^(-beta η)→0≤M→M≤Cm*σ→
      (∀x,0 < map S.law ctx x→∀i,DomainClass (D*σ^(3*beta η)) (PS.domain x i) a)→
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) ∨
      Nonempty (CodedStream (K:=K) (V:=Dual K V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  filter_upwards [eventually_forward_prepared_stage hη hη' c C Cm hc hC hCm,
    eventually_no_high_class hη (c/8) C₀ (8*C) Cm (by positivity) (by positivity) hCm] with σ hf hh
  intro q₀ K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N m l adm S ctx D B M k₀ PS a
    hd hq3 hcard hσ hq hα hN hCs hm8 hD hDhi hlen hm hl hk₀ hB hBhi hM hMhi hcl
  rcases a with b|b|⟨r,s⟩
  · exact Or.inl (hf q₀ K V Ω κ α N m l adm S ctx D B M k₀ PS b
      hd hq3 hcard hσ hq hD hDhi hlen hm hl hk₀ hB hBhi hM hMhi hcl)
  · let : Fintype (ℙ K (Dual K (Dual K (Dual K V)))) :=
      Fintype.ofEquiv (ℙ K (Dual K V)) bidualPoint
    apply Or.inr
    apply hf q₀ K (Dual K V) Ω κ α N m l adm
      (S.changeOrientation swapFlag swapFlag.symm swapFlag.symm_apply_apply)
      ctx D B M k₀ PS.swap b (by simpa using hd) hq3 hcard hσ hq hD hDhi
      hlen hm hl hk₀ hB hBhi hM hMhi
    intro c hc i
    obtain ⟨u,hu1,hu2,hu3,hu4⟩:=hcl c hc i.rev
    exact ⟨u,hu1,hu2,hu3.swap,hu4⟩
  · exfalso
    let t:=m/4
    have ht : 0<t := by dsimp [t];omega
    let : Nonempty (Fin t):=⟨⟨0,ht⟩⟩
    have htm : 1*(4*t)≤ m := by dsimp [t];omega
    have hmt : (m:ℝ)≤8*t := by exact_mod_cast (show m≤8*t by dsimp [t];omega)
    let e:=Fin.castLEOrderEmb htm
    have hJ : 4*σ≤Real.log (153*(Nat.card K:ℝ)^4) := by
      have hl153 : 0≤Real.log 153 := Real.log_nonneg (by norm_num)
      rw [Real.log_mul (by norm_num) (by rw [←hq];positivity),Real.log_pow,←hq,Real.log_exp]
      norm_num only [Nat.cast_ofNat]
      linarith
    have hDn : 0≤D := (Real.rpow_nonneg (by linarith : 0≤σ) _).trans hD
    have hB' : B≤8*C*(t:ℝ)*D*σ^(-beta η) := by
      have hmul:=mul_le_mul_of_nonneg_right hmt (by positivity : 0≤C*D*σ^(-beta η))
      nlinarith
    exact hh K V Ω κ α N t adm (S.reindex e) ctx D _ B M (D*σ^(3*beta η)) (PS.reindex e) r s
      hd hσ hq hα hN (by rw [hq];nlinarith) hCs hD hDhi hB' hMhi hJ
      (fun c hc i=>hcl c hc (e i))
end
end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch_oai := @OAI.SharpRamseyFive.SelectedTuple.eventually_prepared_dispatch_oai
